import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.Crd

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def Ortho (S : Formalism.BasicNotions.HSpace E) : Prop :=
  (∀ a b, S.hT (S.frame a) (S.frame b) = if a = b then 1 else 0) ∧ S.L0 = Submodule.span (𝓞 E) (Set.range S.frame)

theorem ortho_pos (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x)) (N : ℕ) : Ortho (Examples₂.posSpace hstar N) :=
  ⟨fun a b => (Examples₂.stdSpace_gram_apply hstar N (fun _ => false) N 0 a b).trans (by simp [Examples₂.sgn]; rfl), rfl⟩

abbrev co (S : Formalism.BasicNotions.HSpace E) {n : ℕ} (h : S.rank = n) : S.V ≃ₗ[E] (Fin n → E) :=
  S.frame.equivFun.trans (LinearEquiv.funCongrLeft E E (finCongr h).symm)

theorem Ortho.isStd {S : Formalism.BasicNotions.HSpace E} (h : Ortho S) : Formalism.L2.Herm.IsStd S := ⟨S.frame, h.1, h.2⟩

theorem Ortho.gram {S : Formalism.BasicNotions.HSpace E} (h : Ortho S) {n : ℕ} (hn : S.rank = n) :
    S.gram.reindex (finCongr hn) (finCongr hn) = 1 := by
  subst hn
  ext a b
  simpa [HSpace.gram, Matrix.one_apply] using h.1 a b

theorem Ortho.mem_standardLattice_iff_integral_coords {S : Formalism.BasicNotions.HSpace E} (h : Ortho S) {n : ℕ} (hn : S.rank = n) (x : Fin n → E) :
    x ∈ S.L0.map (((co S hn : S.V ≃ₗ[E] (Fin n → E)) : S.V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) ↔
      ∀ j, x j ∈ (algebraMap (𝓞 E) E).range := by
  subst hn
  rw [h.2]
  constructor
  · rintro ⟨v, hv, rfl⟩ j
    have := (Module.Basis.mem_span_iff_repr_mem (𝓞 E) S.frame v).1 hv j
    simpa [co] using this
  · intro hx
    refine ⟨(co S rfl).symm x, (Module.Basis.mem_span_iff_repr_mem (𝓞 E) S.frame _).2 fun j => ?_, (co S rfl).apply_symm_apply x⟩
    have h2 : S.frame.repr ((co S rfl).symm x) j = x j :=
      congrFun ((co S rfl).apply_symm_apply x) j
    rw [h2]
    exact hx j

theorem map_symm_map {S : Formalism.BasicNotions.HSpace E} {n : ℕ} (e : S.V ≃ₗ[E] (Fin n → E)) (L : Submodule (𝓞 E) (Fin n → E)) :
    (L.map ((e.symm : (Fin n → E) →ₗ[E] S.V).restrictScalars (𝓞 E))).map
      ((e : S.V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) = L := by
  ext x
  simp

theorem incl_co {S S' : Formalism.BasicNotions.HSpace E} {n : ℕ} (hn : S.rank = n) (hn' : S'.rank = n - 1) (f : S'.V →ₗ[E] S.V)
    (hf : ∀ (a : Fin S'.rank) (b : Fin S.rank), (a : ℕ) = b → f (S'.frame a) = S.frame b) (x : Fin (n - 1) → E) (j : Fin n) :
    co S hn (f ((co S' hn').symm x)) j = if h : j.1 < n - 1 then x ⟨j.1, h⟩ else 0 := by
  subst hn
  have hs : (co S' hn').symm x = ∑ a : Fin (S.rank - 1), x a • S'.frame (finCongr hn'.symm a) := by
    rw [LinearEquiv.symm_apply_eq]
    funext k
    rw [map_sum, Finset.sum_apply, Finset.sum_eq_single k]
    · simp [co]
    · intro a _ ha
      have : ¬ (a : ℕ) = k := fun h => ha (Fin.ext h)
      simp [co, Finsupp.single_apply, Fin.ext_iff, this]
    · simp
  have hb : ∀ a : Fin (S.rank - 1), f (S'.frame (finCongr hn'.symm a)) = S.frame ⟨a.1, by omega⟩ := fun a => hf _ _ rfl
  rw [hs, map_sum, map_sum]
  simp only [map_smul, hb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hc : ∀ a : Fin (S.rank - 1), co S rfl (S.frame ⟨a.1, by omega⟩) j = if a.1 = j.1 then 1 else 0 := by
    intro a
    simp [co, Fin.ext_iff]
  simp only [hc]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j.1, h⟩]
    · simp
    · intro a _ ha
      rw [if_neg (fun h2 => ha (Fin.ext h2)), mul_zero]
    · simp
  · refine Finset.sum_eq_zero fun a _ => ?_
    rw [if_neg (fun h2 : a.1 = j.1 => h (h2 ▸ a.2)), mul_zero]

end Gen

end GlobalTheory.Mem.Col2.Crd

end

set_option maxHeartbeats 1600000 in

theorem GlobalTheory.Mem.Col2.TC.spaces_in_coordinates : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), Formalism.L2.Herm.StdTied (I.rec7 l Z) ∧ gramP (I.rec7 l Z) = 1 ∧ (∀ x j, iXc (I.rec7 l Z) x j = if h : j.1 < B.R.N B.R.m - 1 then x ⟨j.1, h⟩ else 0) ∧ ∀ i (hi : i ≤ B.R.m), gramN (I.rec7 l Z) i hi = 1 ∧ (∀ x, x ∈ selfDualLatticeCoords (I.rec7 l Z) i hi ↔ ∀ j, x j ∈ (algebraMap (𝓞 B.host.E) B.host.E).range) ∧ ∀ u a, (∀ c, latCrd (I.rec7 l Z) i hi (I.latAt u a i c) = ((I.stp u a i).rep c).1.1.deco.1.L) ∧ ∃ (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi), I.IdY l Z u a i hi eY ∧ ∀ τ z, (I.chain l u a).de i z τ = ((eY z).1 τ).det := by
  intro B X I hI hP l Z
  obtain ⟨hs, hX, hX', -⟩ := hI.spaces
  have oX : ∀ j, Crd.Ortho (B.sp.X j) := fun j => by rw [hX]; exact Crd.ortho_pos hs _
  have oX' : Crd.Ortho B.sp.X' := by rw [hX']; exact Crd.ortho_pos hs _
  refine ⟨⟨fun i _ => (oX i).isStd, oX'.isStd⟩, oX'.gram (rankP (I.rec7 l Z)), fun x j => ?_, fun i hi =>
    ⟨(oX i).gram (rankN (I.rec7 l Z) i hi), fun x => (oX i).mem_standardLattice_iff_integral_coords (rankN (I.rec7 l Z) i hi) x, fun u a => ⟨fun c => ?_, ?_⟩⟩⟩
  · exact Crd.incl_co (S := B.sp.X B.R.m) (S' := B.sp.X') (rankN (I.rec7 l Z) _ le_rfl) (rankP (I.rec7 l Z)) B.sp.iX' hP.iX x j
  · unfold TC.latAt
    rw [dif_pos hi]
    exact Crd.map_symm_map (S := B.sp.X i) (TC.crd B i hi) _
  · exact ⟨Equiv.refl _, fun _ => rfl, fun _ _ => rfl⟩
