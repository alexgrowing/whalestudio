import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolMatchFiniteSetVacuum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetIntegralAdeleMulVecMemLatticeClosureStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorLatticeMulTransposeStableIffStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU
open scoped Classical

noncomputable section
namespace GlobalTheory.FinDecomp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F) in

def idem (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : AF F := pairA F 0 (singleFin v 1)

theorem af_ext' {a b : AF F} (h1 : fstA F a = fstA F b) (h2 : ∀ u : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, evFin F u a = evFin F u b) : a = b :=
  Prod.ext h1 (af_ext fun u => h2 u)

theorem fst_idem (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : fstA F (idem F v) = 0 := rfl

theorem evFin_idem (v u : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : evFin F u (idem F v) = if u = v then 1 else 0 := by
  split_ifs with h
  · subst h; exact evalV_singleFin_self u 1
  · exact evalV_singleFin_ne h 1

theorem idem_mul_self (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : idem F v * idem F v = idem F v :=
  af_ext' (by simp [map_mul, fst_idem]) fun u => by rw [map_mul, evFin_idem]; split_ifs <;> simp

variable (F) in

def idemS (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) : AF F := ∑ v ∈ S, idem F v

theorem fst_idemS (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) : fstA F (idemS F S) = 0 := by
  simp [idemS, map_sum, fst_idem]

theorem evFin_idemS (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) (u : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) : evFin F u (idemS F S) = if u ∈ S then 1 else 0 := by
  simp [idemS, map_sum, evFin_idem, Finset.sum_ite_eq]

theorem idemS_mul_self (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) : idemS F S * idemS F S = idemS F S :=
  af_ext' (by simp [map_mul, fst_idemS]) fun u => by rw [map_mul, evFin_idemS]; split_ifs <;> simp

theorem idem_mul_idemS_of_mem {w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} {S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)} (h : w ∈ S) : idem F w * idemS F S = idem F w :=
  af_ext' (by simp [map_mul, fst_idemS, fst_idem]) fun u => by
    rw [map_mul, evFin_idemS, evFin_idem]; split_ifs with h1 h2 <;> simp_all

theorem idem_mul_idemS_of_notMem {w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} {S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)} (h : w ∉ S) : idem F w * idemS F S = 0 :=
  af_ext' (by simp [map_mul, fst_idemS, fst_idem]) fun u => by
    rw [map_mul, evFin_idemS, evFin_idem, map_zero]; split_ifs with h1 h2 <;> simp_all

theorem mul_idem_of_evFin {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} {a : AF F} (h : evFin F v a = 0) : a * idem F v = 0 :=
  af_ext' (by simp [map_mul, fst_idem]) fun u => by
    rw [map_mul, evFin_idem, map_zero]; split_ifs with hu
    · subst hu; simpa using h
    · simp

theorem idem_mul_of_at {w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} {a : AF F} (h : At (evFin F w) a) : idem F w * a = a := by
  have := h (1 - idem F w) (by simp [evFin_idem])
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at this
  exact this.symm

end GlobalTheory.FinDecomp
end

noncomputable section
namespace GlobalTheory.FinDecomp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def phi (e : AF F) (M : Matrix (Fin n) (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E) := (1 - e) • 1 + e • M

theorem phi_mul {e : AF F} (he : e * e = e) (M N : Matrix (Fin n) (Fin n) (AE F E)) :
    phi e (M * N) = phi e M * phi e N := by
  have h1 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  have h2 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h3 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  simp only [phi, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one,
    h1, h2, h3, he, zero_smul, add_zero, zero_add]

theorem phi_mul_orth {e f : AF F} (hef : e * f = 0) (M : Matrix (Fin n) (Fin n) (AE F E)) :
    phi e M * phi f M = phi (e + f) M := by
  have hfe : f * e = 0 := by rw [mul_comm, hef]
  have h1 : (1 - f) * (1 - e) = 1 - (e + f) := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hfe, sub_zero]; ring
  have h2 : (1 - f) * e = e := by rw [sub_mul, one_mul, hfe, sub_zero]
  have h3 : f * (1 - e) = f := by rw [mul_sub, mul_one, hfe, sub_zero]
  simp only [phi, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one,
    h1, h2, h3, hfe, zero_smul, add_zero, add_smul]
  abel

theorem phi_one (M : Matrix (Fin n) (Fin n) (AE F E)) : phi (1 : AF F) M = M := by simp [phi]

theorem phi_zero (M : Matrix (Fin n) (Fin n) (AE F E)) : phi (0 : AF F) M = 1 := by simp [phi]

theorem phi_sub_one (e : AF F) (M : Matrix (Fin n) (Fin n) (AE F E)) : phi e M - 1 = e • (M - 1) := by
  simp only [phi, sub_smul, one_smul, smul_sub]; abel

theorem smul_phi_compl {a e : AF F} (h : a * e = 0) (M : Matrix (Fin n) (Fin n) (AE F E)) :
    a • phi (1 - e) M = a • M := by
  simp only [phi, smul_add, smul_smul, sub_sub_cancel, h, zero_smul, zero_add, mul_sub, mul_one, sub_zero]

theorem phi_unitary {σ : E →ₐ[F] E} {e : AF F} (he : e * e = e) {J M : Matrix (Fin n) (Fin n) (AE F E)}
    (hM : Mᵀ * J * M.map (cA σ) = J) : (phi e M)ᵀ * J * (phi e M).map (cA σ) = J := by
  have h1 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  have h2 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h3 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have hm : (phi e M).map (cA σ) = (1 - e) • 1 + e • M.map (cA σ) := by
    ext i j
    simp only [phi, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, map_add, map_smul, Matrix.one_apply]
    split_ifs <;> simp
  have ht : (phi e M)ᵀ = (1 - e) • 1 + e • Mᵀ := by simp [phi, Matrix.transpose_add, Matrix.transpose_smul]
  rw [hm, ht]
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one,
    h1, h2, h3, he, zero_smul, add_zero, zero_add, ← Matrix.mul_assoc, hM]
  rw [← add_smul, sub_add_cancel, one_smul]

section Loc

variable {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E}

theorem mat_mul (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one : mat (1 : UA σ J) = 1 := rfl

theorem mat_mul_inv (g : UA σ J) : mat g * mat g⁻¹ = 1 := Units.mul_inv g.1

theorem mat_inv_mul (g : UA σ J) : mat g⁻¹ * mat g = 1 := Units.inv_mul g.1

theorem ua_ext {g h : UA σ J} (e : mat g = mat h) : g = h := Subtype.ext (Units.ext e)

def loc (e : AF F) (he : e * e = e) (g : UA σ J) : UA σ J :=
  ⟨⟨phi e (mat g), phi e (mat g⁻¹), by rw [← phi_mul he, mat_mul_inv]; simp only [phi]; rw [← add_smul, sub_add_cancel, one_smul],
      by rw [← phi_mul he, mat_inv_mul]; simp only [phi]; rw [← add_smul, sub_add_cancel, one_smul]⟩, phi_unitary he g.2⟩

theorem mat_loc (e : AF F) (he : e * e = e) (g : UA σ J) : mat (loc e he g) = phi e (mat g) := rfl

theorem mat_loc_inv (e : AF F) (he : e * e = e) (g : UA σ J) : mat (loc e he g)⁻¹ = phi e (mat g⁻¹) := rfl

end Loc

end GlobalTheory.FinDecomp
end

noncomputable section
namespace GlobalTheory.FinDecomp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E}

theorem idemS_insert {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} {S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)} (h : v ∉ S) :
    idemS F (insert v S) = idem F v + idemS F S := Finset.sum_insert h

theorem mat_prod_loc (g : UA σ J) : ∀ l : List (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), l.Nodup →
    mat (l.map fun v => loc (idem F v) (idem_mul_self v) g).prod = phi (idemS F l.toFinset) (mat g)
  | [], _ => by simp [idemS, phi_zero, mat_one]
  | v :: t, hl => by
    rw [List.nodup_cons] at hl
    have hv : v ∉ t.toFinset := by simpa using hl.1
    rw [List.map_cons, List.prod_cons, mat_mul, mat_prod_loc g t hl.2, mat_loc, List.toFinset_cons,
      idemS_insert hv, phi_mul_orth (idem_mul_idemS_of_notMem hv)]

theorem exists_prod_local_mul_latStab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a'), G.IsGood B →
    ∀ h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J,
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat h - 1) = 0) →
    ∀ T₀ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), ∃ (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F))
      (l : List (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)) (k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J),
    T₀ ⊆ S ∧ (∀ x ∈ l, x.1 ∈ S ∧ x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F x.1)) ∧
    h = (l.map Prod.snd).prod * k ∧
    (∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) ∧
    (∀ w ∈ S, ∀ u : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) ∧
    (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V G.W w) ∧
    (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV G.V' G.W w) := by
  intro F E _ _ _ _ _ σ B a a' G hG h hinf T₀
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.exists_finset_integral_adele_mulVec_mem_lattice_closure F E _ (mat h) G.W.L hG.hW.lat
  obtain ⟨S₂, hS₂⟩ := GlobalTheory.T.exists_finset_integral_adele_mulVec_mem_lattice_closure F E _ (mat h⁻¹) G.W.L hG.hW.lat
  set S := T₀ ∪ S₁ ∪ S₂ with hSdef
  have heS : idemS F S * idemS F S = idemS F S := idemS_mul_self S
  have heS' : (1 - idemS F S) * (1 - idemS F S) = 1 - idemS F S := by
    rw [sub_mul, one_mul, mul_sub, mul_one, heS, sub_self, sub_zero]
  have horth : idemS F S * (1 - idemS F S) = 0 := by rw [mul_sub, mul_one, heS, sub_self]
  set k := loc (1 - idemS F S) heS' h with hk
  have hl : ((S.toList.map fun v => (v, loc (idem F v) (idem_mul_self v) h)).map Prod.snd) =
      S.toList.map fun v => loc (idem F v) (idem_mul_self v) h := by
    rw [List.map_map]; rfl
  have hnot : ∀ w ∉ S, ∀ u : AF F, At (evFin F w) u → u * idemS F S = 0 := by
    intro w hw u hu
    rw [← idem_mul_of_at hu, mul_comm (idem F w), mul_assoc, idem_mul_idemS_of_notMem hw, mul_zero]
  have hgood : ∀ w ∉ S, ∀ (X : ℕ) (Xs : Spc F E X), ∀ γ, γ * (mat k)ᵀ ∈ latAtV Xs G.W w ↔ γ ∈ latAtV Xs G.W w := by
    intro w hw X Xs γ
    have hw1 : w ∉ S₁ := fun h' => hw (by simp [hSdef, h'])
    have hw2 : w ∉ S₂ := fun h' => hw (by simp [hSdef, h'])
    refine GlobalTheory.T.tensorLattice_mul_transpose_stable_iff F E X (a + a') Xs G.W w (mat k) (mat k⁻¹) (mat_inv_mul k) ?_ ?_ γ
    · intro u hu hint y hy
      rw [← Matrix.smul_mulVec, mat_loc, smul_phi_compl (hnot w hw u hu), Matrix.smul_mulVec]
      exact hS₁ w hw1 u hu hint y hy
    · intro u hu hint y hy
      rw [← Matrix.smul_mulVec, mat_loc_inv, smul_phi_compl (hnot w hw u hu), Matrix.smul_mulVec]
      exact hS₂ w hw2 u hu hint y hy
  refine ⟨S, S.toList.map fun v => (v, loc (idem F v) (idem_mul_self v) h), k, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx; simp [hSdef, hx]
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
    refine ⟨Finset.mem_toList.1 hv, ?_⟩
    intro u hu
    show u • (mat (loc (idem F v) (idem_mul_self v) h) - 1) = 0
    rw [mat_loc, phi_sub_one, smul_smul, mul_idem_of_evFin hu, zero_smul]
  · apply ua_ext
    rw [mat_mul, hl, mat_prod_loc h _ S.nodup_toList, Finset.toList_toFinset, hk, mat_loc, phi_mul_orth horth,
      add_sub_cancel, phi_one]
  · intro u hu
    rw [hk, mat_loc, phi_sub_one, smul_comm, hinf u hu, smul_zero]
  · intro w hw u hu
    have hu' := idem_mul_of_at hu
    have : u * (1 - idemS F S) = 0 := by
      calc u * (1 - idemS F S) = (idem F w * u) * (1 - idemS F S) := by rw [hu']
        _ = u * (idem F w - idem F w * idemS F S) := by ring
        _ = 0 := by rw [idem_mul_idemS_of_mem hw, sub_self, mul_zero]
    rw [hk, mat_loc, phi_sub_one, smul_smul, this, zero_smul]
  · exact fun w hw => hgood w hw a G.V
  · exact fun w hw => hgood w hw a' G.V'

end GlobalTheory.FinDecomp
end
