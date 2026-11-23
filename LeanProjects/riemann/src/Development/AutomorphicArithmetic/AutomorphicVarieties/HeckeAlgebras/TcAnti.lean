import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd

noncomputable section

open Matrix ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace UpperTheory.V.Hi

structure IwaData (G : Type) [Group G] where
  Nf : Subgroup G
  Tf : Subgroup G
  N : Subgroup G
  T : Subgroup G
  Tc : ℕ → Subgroup G
  Nm : ℕ → Subgroup G
  P : Submonoid G
  z : G

namespace IwaData

variable {G : Type} [Group G] (D : IwaData G)

structure Ax : Prop where
  N_le : D.N ≤ D.Nf
  T_le : D.T ≤ D.Tf
  P_le : ∀ a ∈ D.P, a ∈ D.Tf
  z_mem : D.z ∈ D.P
  Tc_le : ∀ c, D.Tc c ≤ D.T
  Tc_anti : Antitone D.Tc
  Nm_anti : Antitone D.Nm
  comm : ∀ s ∈ D.Tf, ∀ t ∈ D.Tf, s * t = t * s
  Tf_Nf : ∀ t ∈ D.Tf, ∀ x ∈ D.Nf, t * x * t⁻¹ ∈ D.Nf
  T_N : ∀ t ∈ D.T, ∀ x ∈ D.N, t * x * t⁻¹ ∈ D.N
  T_Nm : ∀ c, ∀ t ∈ D.T, ∀ y ∈ D.Nm c, t * y * t⁻¹ ∈ D.Nm c
  P_N : ∀ a ∈ D.P, ∀ x ∈ D.N, a * x * a⁻¹ ∈ D.N
  P_Nm : ∀ c, ∀ a ∈ D.P, ∀ y ∈ D.Nm c, a⁻¹ * y * a ∈ D.Nm c
  z_Nm : ∀ c, ∀ y ∈ D.Nm c, D.z⁻¹ * y * D.z ∈ D.Nm (c + 1)
  swap : ∀ c, ∀ y ∈ D.Nm c, ∀ x ∈ D.N, ∃ x' ∈ D.N, ∃ t ∈ D.Tc c, ∃ y' ∈ D.Nm c, y * x = x' * t * y'
  uniq : ∀ x ∈ D.Nf, ∀ t ∈ D.Tf, ∀ y ∈ D.Nm 0, x * t * y = 1 → x = 1 ∧ t = 1
  fin_N : ∀ a ∈ D.P, (D.N.map (MulAut.conj a).toMonoidHom).relIndex D.N ≠ 0
  fin_Nm : ∀ c, (D.Nm c).relIndex (D.Nm 0) ≠ 0
  fin_Tc : ∀ c, (D.Tc c).relIndex D.T ≠ 0
  exh : ∀ x ∈ D.Nf, ∃ k : ℕ, D.z ^ k * x * (D.z ^ k)⁻¹ ∈ D.N
  exists_pow_mul_inv_mem : ∀ a ∈ D.P, ∃ k : ℕ, D.z ^ k * a⁻¹ ∈ D.P
  gen : ∀ t ∈ D.Tf, ∃ s ∈ D.T, ∃ a ∈ D.P, ∃ b ∈ D.P, t = s * a * b⁻¹

def toIwa (h : D.Ax) : Iwa G :=
  ⟨D.Nf, D.Tf, D.N, D.T, D.Tc, D.Nm, D.P, D.z, h.N_le, h.T_le, h.P_le, h.z_mem, h.Tc_le, h.Tc_anti, h.Nm_anti, h.comm, h.Tf_Nf,
    h.T_N, h.T_Nm, h.P_N, h.P_Nm, h.z_Nm, h.swap, h.uniq, h.fin_N, h.fin_Nm, h.fin_Tc, h.exh, h.exists_pow_mul_inv_mem, h.gen⟩

end IwaData

def piData {σ : Type} {G : σ → Type} [∀ v, Group (G v)] (I : ∀ v, Iwa (G v)) : IwaData (∀ v, G v) where
  Nf := Subgroup.pi Set.univ fun v => (I v).Nf
  Tf := Subgroup.pi Set.univ fun v => (I v).Tf
  N := Subgroup.pi Set.univ fun v => (I v).N
  T := Subgroup.pi Set.univ fun v => (I v).T
  Tc c := Subgroup.pi Set.univ fun v => (I v).Tc c
  Nm c := Subgroup.pi Set.univ fun v => (I v).Nm c
  P := Submonoid.pi Set.univ fun v => (I v).P
  z v := (I v).z

section Lin

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)

def Kc (c : ℕ) : Subgroup (GL (Fin n) k) :=
  (GeneralLinearGroup.map (n := Fin n) (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c))).ker.map
    (GeneralLinearGroup.map (algebraMap 𝒪[k] k))

def unif : kˣ := Classical.epsilon fun x : kˣ => valuation k (x : k) = uniformizer k

def Uo : Subgroup kˣ where
  carrier := {t | valuation k (t : k) = 1}
  one_mem' := by simp
  mul_mem' {s t} hs ht := by
    have h1 : valuation k (s : k) = 1 := hs
    have h2 : valuation k (t : k) = 1 := ht
    simp [h1, h2]
  inv_mem' {t} ht := by
    have h1 : valuation k (t : k) = 1 := ht
    simp [h1]

def Uc (c : ℕ) : Subgroup kˣ :=
  (Units.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ c)).toMonoidHom).ker.map
    (Units.map (algebraMap 𝒪[k] k).toMonoidHom)

def upow (a : Fin n → ℤ) : GL (Fin n) k := diagT k (Fin n) fun i => unif k ^ a i

def al (j : ℕ) : GL (Fin n) k := upow k n fun i => if (i : ℕ) < j then 1 else 0

def glData : IwaData (GL (Fin n) k) where
  Nf := unipB k (Fin n)
  Tf := (diagT k (Fin n)).range
  N := unipB k (Fin n) ⊓ KO k (Fin n)
  T := (torusO k (Fin n)).map (diagT k (Fin n))
  Tc c := (torusO k (Fin n)).map (diagT k (Fin n)) ⊓ Kc k n (c + 1)
  Nm c := (unipB k (Fin n)).comap (GlobalTheory.CuspRep.invT n k) ⊓ Kc k n (c + 1)
  P :=
    { carrier := {g | ∃ a : Fin n → ℤ, Antitone a ∧ g = upow k n a}
      one_mem' := ⟨0, fun _ _ _ => le_rfl, by
        rw [upow, ← (diagT k (Fin n)).map_one]; congr 1; funext i; simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        refine ⟨a + b, ha.add hb, ?_⟩
        rw [upow, upow, upow, ← map_mul]
        congr 1
        funext i
        simp [_root_.zpow_add] }
  z := upow k n fun i => (n : ℤ) - 1 - (i : ℕ)

theorem al_mem (j : ℕ) : al k n j ∈ (glData k n).P :=
  ⟨_, fun i i' h => by
    have : (i : ℕ) ≤ i' := h
    change (if (i' : ℕ) < j then (1 : ℤ) else 0) ≤ if (i : ℕ) < j then 1 else 0
    split_ifs <;> omega, rfl⟩

def eT (i : Fin n) : Uo k →* (glData k n).T where
  toFun y := ⟨diagT k (Fin n) (Pi.mulSingle i (y : kˣ)), Pi.mulSingle i (y : kˣ), fun j => by
    by_cases h : j = i
    · subst h
      rw [Pi.mulSingle_eq_same]; exact y.2
    · simp [Pi.mulSingle_eq_of_ne h], rfl⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp [Pi.mulSingle_mul])

end Lin

end UpperTheory.V.Hi
