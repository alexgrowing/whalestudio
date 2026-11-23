import CompanionTheory.AutomorphicTheory.HeckeStandardModules.ExistsDenFin
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.HeckeA
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.HeckeStdStatement
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.UG Formalism.L2 CompanionTheory.Split CompanionTheory.HeckeA

noncomputable section

namespace CompanionTheory.L3H

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

local notation3 "L⁺" => maximalRealSubfield L

section Loc

variable (s : SplitPlace L) (n)

def dg {ϖ : s.v.adicCompletion L⁺} (h0 : ϖ ≠ 0) (k : ℕ) : GL (Fin n) (s.v.adicCompletion L⁺) :=
  ⟨diagJ n ϖ k, Matrix.diagonal fun i => if (i : ℕ) < k then ϖ⁻¹ else 1,
    by rw [diagJ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; split_ifs <;> simp [h0],
    by rw [diagJ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; split_ifs <;> simp [h0]⟩

variable {n}

theorem tSet_iff {ϖ : s.v.adicCompletion L⁺} (h0 : ϖ ≠ 0) (k : ℕ) (x : Formalism.AUTREP.GAf L n) :
    x ∈ Formalism.AUTREP.tSet L n s ϖ k ↔ ∃ h ∈ DoubleCoset.doubleCoset (dg n s h0 k) (KL s n : Set _) (KL s n), emb s n h = x := by
  constructor
  · rintro ⟨hx, a, ha, b, hb, e⟩
    refine ⟨s.loc n x, DoubleCoset.mem_doubleCoset.2 ⟨a, ha, b, hb, Units.ext ?_⟩, emb_loc s hx⟩
    rw [Units.val_mul, Units.val_mul]
    exact e
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hh
    exact ⟨emb_triv s _, a, ha, b, hb, by rw [loc_emb]; rfl⟩

theorem triv_compl {B : Set (HeightOneSpectrum (𝓞 L⁺))} (hs : s.v ∉ B) {x : Formalism.AUTREP.GAf L n}
    (hx : TrivOutside {s.v} x) : TrivOutside Bᶜ x := fun w hw => hx w fun h => hw (by rw [Set.mem_singleton_iff.1 h]; exact hs)

variable {s}

theorem emb_mem_J {J : Subgroup (Formalism.AUTREP.GAf L n)} {χ : J →* ℂˣ} {B : Set (HeightOneSpectrum (𝓞 L⁺))}
    (hJ : NG.HypOutside J χ B) (hs : s.v ∉ B) (h : GL (Fin n) (s.v.adicCompletion L⁺)) :
    emb s n h ∈ J ↔ h ∈ KL s n := by
  rw [(hJ _ (triv_compl s hs (emb_triv s h))).1, mem_Umax_iff s (emb_triv s h), loc_emb]

theorem chi_emb {J : Subgroup (Formalism.AUTREP.GAf L n)} {χ : J →* ℂˣ} {B : Set (HeightOneSpectrum (𝓞 L⁺))}
    (hJ : NG.HypOutside J χ B) (hs : s.v ∉ B) {h : GL (Fin n) (s.v.adicCompletion L⁺)} (hm : emb s n h ∈ J) :
    χ ⟨_, hm⟩ = 1 := (hJ _ (triv_compl s hs (emb_triv s h))).2 hm

end Loc

section TypeSp

variable {ρ : Representation ℂ (GQ L n) W} {J : Subgroup (Formalism.AUTREP.GAf L n)} {χ : J →* ℂˣ}
  {B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {s : SplitPlace L}

theorem inv_of_mem (hJ : NG.HypOutside J χ B) (hs : s.v ∉ B) {f : Formalism.AUTREP.GAf L n → W} (hf : f ∈ NG.TypeSp ρ J χ) :
    Inv (emb s n) (KL s n) f := fun g k hk => by
  have hm := (emb_mem_J hJ hs k).2 hk
  have h2 := congrFun (hf.2 ⟨_, hm⟩) g
  rw [chi_emb hJ hs hm, Units.val_one, one_smul] at h2
  exact h2

theorem heckeD_eq (hJ : NG.HypOutside J χ B) (hs : s.v ∉ B) {f : Formalism.AUTREP.GAf L n → W} (hf : Inv (emb s n) (KL s n) f)
    (d : GL (Fin n) (s.v.adicCompletion L⁺)) {D : Set (Formalism.AUTREP.GAf L n)}
    (hD : ∀ x, x ∈ D ↔ ∃ h ∈ DoubleCoset.doubleCoset d (KL s n : Set _) (KL s n), emb s n h = x) :
    NG.heckeD J D f = op (emb s n) (KL s n) (dosetInd ℂ (KL s n) d) f :=
  funext fun g => coset_sum_eq (emb s n) (KL s n) J (emb_mem_J hJ hs) d hf g hD

theorem comm_KL (s : SplitPlace L) : IsCommensurated (KL s n) := Final.GLintComm L⁺ s.v n

theorem dosetInd_mem (s : SplitPlace L) (d : GL (Fin n) (s.v.adicCompletion L⁺)) : dosetInd ℂ (KL s n) d ∈ Hecke ℂ (KL s n) :=
  Final.DosetIndMem _ _ ℂ d

theorem op_equiv (hJ : NG.HypOutside J χ B) (hs : s.v ∉ B) (hϖ : ∃ ϖ : s.v.adicCompletion L⁺, Valued.v ϖ = WithZero.exp (-1 : ℤ))
    {f : Formalism.AUTREP.GAf L n → W} (hf : f ∈ NG.TypeSp ρ J χ) (d : GL (Fin n) (s.v.adicCompletion L⁺)) (κ : J) (g) :
    op (emb s n) (KL s n) (dosetInd ℂ (KL s n) d) f (g * κ) = ((χ κ : ℂˣ) : ℂ) • op (emb s n) (KL s n) (dosetInd ℂ (KL s n) d) f g := by
  obtain ⟨ϖ, hϖ⟩ := hϖ
  have hk : ∀ k ∈ KL s n, s.loc n κ * k * (s.loc n κ)⁻¹ ∈ KL s n := fun k hk => by
    refine (emb_mem_J hJ hs _).1 ?_
    rw [← conj_emb]
    exact J.mul_mem (J.mul_mem κ.2 ((emb_mem_J hJ hs k).2 hk)) (J.inv_mem κ.2)
  obtain ⟨u, hu, hcu⟩ := normaliser s hϖ _ hk
  exact op_conj (emb s n) (dosetInd_mem s d).1 (inv_of_mem hJ hs hf) hu (fun h => by rw [conj_emb, hcu])
    (fun g => congrFun (hf.2 κ) g) (comm_KL s) (dosetInd_mem s d) g

theorem op_mem (hJ : NG.HypOutside J χ B) (hs : s.v ∉ B) (hϖ : ∃ ϖ : s.v.adicCompletion L⁺, Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (hN : ∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1)
    {f : Formalism.AUTREP.GAf L n → W} (hf : f ∈ NG.TypeSp ρ J χ) (d : GL (Fin n) (s.v.adicCompletion L⁺)) :
    op (emb s n) (KL s n) (dosetInd ℂ (KL s n) d) f ∈ NG.TypeSp ρ J χ := by
  obtain ⟨S, hS⟩ := exists_sum (W := W) (emb s n) (comm_KL s) (dosetInd_mem s d)
  obtain ⟨N, hN0, hN⟩ := hN
  refine ⟨⟨fun γ g => ?_, N, hN0, fun κ hκ g => ?_⟩, fun κ => funext fun g => op_equiv hJ hs hϖ hf d κ g⟩
  · rw [hS, hS, map_sum]
    exact Finset.sum_congr rfl fun c _ => by rw [mul_assoc, hf.1.1, map_smul]
  · obtain ⟨hm, h1⟩ := hN κ hκ
    have := op_equiv hJ hs hϖ hf d ⟨κ, hm⟩ g
    rwa [h1, Units.val_one, one_smul] at this

end TypeSp

section Same

variable {J : Subgroup (Formalism.AUTREP.GAf L n)} {χ : J →* ℂˣ} {B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))}

theorem tSet_same (s s' : SplitPlace L) (hv : s'.v = s.v) {ϖ' : s'.v.adicCompletion L⁺} (h0 : ϖ' ≠ 0) (k : ℕ) :
    ∃ d : GL (Fin n) (s.v.adicCompletion L⁺), ∀ x, x ∈ Formalism.AUTREP.tSet L n s' ϖ' k ↔
      ∃ h ∈ DoubleCoset.doubleCoset d (KL s n : Set _) (KL s n), emb s n h = x := by
  obtain ⟨v, i⟩ := s'
  obtain rfl : v = s.v := hv
  let s' : SplitPlace L := ⟨s.v, i⟩
  have hK : ∀ a ∈ KL s' n, s.loc n (emb s' n a) ∈ KL s n := fun a ha =>
    (mem_Umax_iff s (emb_triv s' a)).1 ((mem_Umax_iff s' (emb_triv s' a)).2 (by rwa [loc_emb]))
  have hK' : ∀ a ∈ KL s n, s'.loc n (emb s n a) ∈ KL s' n := fun a ha =>
    (mem_Umax_iff s' (emb_triv s a)).1 ((mem_Umax_iff s (emb_triv s a)).2 (by rwa [loc_emb]))
  refine ⟨s.loc n (emb s' n (dg n s' h0 k)), fun x => ?_⟩
  rw [tSet_iff s' h0]
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hh
    refine ⟨_, DoubleCoset.mem_doubleCoset.2 ⟨_, hK a ha, _, hK b hb, rfl⟩, ?_⟩
    rw [map_mul, map_mul, map_mul, map_mul, emb_loc s (emb_triv s' a), emb_loc s (emb_triv s' _),
      emb_loc s (emb_triv s' b)]
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hh
    refine ⟨s'.loc n (emb s n a) * dg n s' h0 k * s'.loc n (emb s n b),
      DoubleCoset.mem_doubleCoset.2 ⟨_, hK' a ha, _, hK' b hb, rfl⟩, ?_⟩
    rw [map_mul, map_mul, map_mul, map_mul, emb_loc s' (emb_triv s a), emb_loc s' (emb_triv s b),
      emb_loc s (emb_triv s' _)]

end Same

section Int

variable {R : Type} [CommRing R] [Algebra R ℂ]

theorem integral_of_module [Module R W] [IsScalarTower R ℂ W] [IsNoetherianRing R] (N : Submodule R W) (hN : N ≠ ⊥)
    (hfg : N.FG) (ν : ℂ) (hν : ∀ w ∈ N, ν • w ∈ N) : IsIntegral R ν :=
  isIntegral_of_smul_mem_submodule N hN hfg ν hν

end Int

end CompanionTheory.L3H
