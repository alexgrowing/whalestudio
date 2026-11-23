import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemChainVecsDet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LabelEqOfSuppAdds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesEqProdOfParabolicInductionChainStatement

noncomputable section

namespace GlobalTheory.SerSys.TameGen

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp CategoryTheory
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

def IsSC (ρ : GLRep g) : Prop := 0 < ρ.1 ∧ IsIrrRep ρ.2.ρ ∧ PRep.IsSupercuspidal ρ.2.ρ

def Inflates {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) ℚ_[g]) V)
    (τ : FDRep ℂ (Gn g n)) : Prop :=
  ∃ φ : τ →ₗ[ℂ] V, φ ≠ 0 ∧ ∀ (k : GL (Fin n) ℤ_[g]) (w : τ), φ (τ.ρ (red g n k) w) = π (inc g n k) (φ w)

def liftPoly (teich : Formalism.CyclotomicNorms.Fbar g → ℂ) (f : (ZMod g)[X]) : ℂ[X] :=
  ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (teich x)).prod

def SupportCompat {LP : Type} (ine : LP → ℂ[X]) (rec : GLRep g → LP) : Prop :=
  ∀ π : GLRep g, IsIrrRep π.2.ρ → PRep.IsSmooth π.2.ρ →
    ∃ L : List (GLRep g), InInd π L ∧ (∀ ρ ∈ L, IsSC ρ) ∧ ine (rec π) = (L.map fun ρ => ine (rec ρ)).prod

def DepthZeroCuspidal (g : ℕ) [Fact g.Prime] : Prop :=
  ∀ ρ : GLRep g, IsSC ρ → fixK1 ρ.2.ρ ≠ ⊥ → FiniteGL.IsCuspidal (repK ρ.2.ρ)

def Pinned (S : Sys g) (teich : Formalism.CyclotomicNorms.Fbar g → ℂ) {LP : Type} (ine : LP → ℂ[X]) (rec : GLRep g → LP) : Prop :=
  ∀ ρ : GLRep g, IsSC ρ → ∀ τ : FDRep ℂ (Gn g ρ.1), Simple τ → FiniteGL.IsCuspidal τ.ρ → Inflates ρ.2.ρ τ →
    ∀ f, Representation.asAlgebraHom τ.ρ (S.e ρ.1 f) = 1 → ine (rec ρ) = liftPoly teich f

theorem liftPoly_one (teich : Formalism.CyclotomicNorms.Fbar g → ℂ) : liftPoly teich (1 : (ZMod g)[X]) = 1 := by
  simp [liftPoly, Formalism.CyclotomicNorms.rootsBar]

theorem liftPoly_mul (teich : Formalism.CyclotomicNorms.Fbar g → ℂ) {f f' : (ZMod g)[X]} (hf : f ≠ 0) (hf' : f' ≠ 0) :
    liftPoly teich (f * f') = liftPoly teich f * liftPoly teich f' := by
  unfold liftPoly Formalism.CyclotomicNorms.rootsBar
  rw [Polynomial.map_mul, roots_mul (mul_ne_zero (map_ne_zero hf) (map_ne_zero hf')), Multiset.map_add,
    Multiset.prod_add]

theorem Has.monic {S : Sys g} {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) ℚ_[g]) V} {f : (ZMod g)[X]} (h : Has S π f) : f.Monic := by
  obtain ⟨v, -, hv⟩ := h
  refine (S.label n f fun e => hv ?_).1
  simp [e, actK]

theorem exists_simple {G W : Type} [Group G] [Fintype G] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W)
    (e : MonoidAlgebra ℂ G) (he : ∀ a, e * a = a * e) (w : W) (hw : w ≠ 0) (hew : σ.asAlgebraHom e w = w) :
    ∃ (τ : FDRep ℂ G) (φ : τ →ₗ[ℂ] W), Simple τ ∧ Function.Injective φ ∧ (∀ x u, φ (τ.ρ x u) = σ x (φ u)) ∧
      Representation.asAlgebraHom τ.ρ e = 1 := by
  let P : Submodule ℂ W → Prop := fun U => U ≠ ⊥ ∧ FiniteDimensional ℂ U ∧ (∀ x, ∀ u ∈ U, σ x u ∈ U) ∧
    ∀ u ∈ U, σ.asAlgebraHom e u = u
  have hex : ∃ m, ∃ U, P U ∧ Module.finrank ℂ U = m := by
    refine ⟨_, Submodule.span ℂ (Set.range fun x => σ x w), ⟨?_, ?_, ?_, ?_⟩, rfl⟩
    · intro h
      exact hw (by simpa using (Submodule.span_eq_bot.1 h) _ ⟨1, rfl⟩)
    · exact FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    · intro x u hu
      refine (show _ ≤ Submodule.comap (σ x) (Submodule.span ℂ (Set.range fun x => σ x w)) from
        Submodule.span_le.2 ?_) hu
      rintro _ ⟨y, rfl⟩
      exact Submodule.subset_span ⟨x * y, by simp⟩
    · intro u hu
      refine (show _ ≤ LinearMap.eqLocus (σ.asAlgebraHom e) LinearMap.id from Submodule.span_le.2 ?_) hu
      rintro _ ⟨y, rfl⟩
      show σ.asAlgebraHom e (σ y w) = σ y w
      rw [← Representation.asAlgebraHom_single_one, ← Module.End.mul_apply, ← map_mul, he, map_mul,
        Module.End.mul_apply, hew]
  obtain ⟨U, ⟨h0, hfin, hst, hfix⟩, hm⟩ := Nat.find_spec hex
  have hmin : ∀ U', P U' → Module.finrank ℂ U ≤ Module.finrank ℂ U' := fun U' h =>
    hm ▸ Nat.find_min' hex ⟨U', h, rfl⟩
  let σU : Representation ℂ G U := PRep.sub σ U hst
  have hirr : IsIrrRep σU := by
    refine ⟨Submodule.nontrivial_iff_ne_bot.2 h0, fun T hT => or_iff_not_imp_left.2 fun hT0 => ?_⟩
    have hP : P (T.map U.subtype) := by
      refine ⟨fun h => hT0 (Submodule.map_injective_of_injective U.injective_subtype (by simpa using h)), inferInstance, ?_, ?_⟩
      · rintro x _ ⟨u, hu, rfl⟩
        exact ⟨_, hT x u hu, rfl⟩
      · rintro _ ⟨u, -, rfl⟩
        exact hfix _ u.2
    have := hmin _ hP
    rw [Submodule.finrank_map_subtype_eq] at this
    exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le T) this)
  refine ⟨FDRep.of σU, U.subtype, ?_, U.injective_subtype, fun _ _ => rfl, ?_⟩
  · have := (Model.isIrrRep_iff σU).1 hirr
    rw [FDRep.simple_iff_char_is_norm_one]
    have hc : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    have := invertibleOfNonzero hc
    have h := Representation.char_orthonormal σU σU
    rw [if_pos ⟨Representation.Equiv.refl σU⟩, inv_mul_eq_one₀ hc] at h
    exact h.symm
  · refine LinearMap.ext fun u => Subtype.ext ?_
    refine Eq.trans ?_ (hfix _ u.2)
    rw [alg_apply, alg_apply]
    exact (Submodule.coe_sum _ _ _).trans rfl

theorem exists_simple_of_has (S : Sys g) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (f : (ZMod g)[X]) (h : Has S π f) :
    ∃ (τ : FDRep ℂ (Gn g n)) (φ : τ →ₗ[ℂ] fixK1 π), Simple τ ∧ Function.Injective φ ∧
      (∀ x u, φ (τ.ρ x u) = repK π x (φ u)) ∧ Representation.asAlgebraHom τ.ρ (S.e n f) = 1 := by
  obtain ⟨v, hv, hne⟩ := h
  refine exists_simple (repK π) (S.e n f) (S.central n f) ((repK π).asAlgebraHom (S.e n f) ⟨v, hv⟩)
    (fun e => hne ?_) ?_
  · rw [← repK_alg π _ ⟨v, hv⟩, e]; rfl
  · rw [← Module.End.mul_apply, ← map_mul, S.idem]

theorem ine_eq_of_isSC (S : Sys g) (teich : Formalism.CyclotomicNorms.Fbar g → ℂ) {LP : Type} (ine : LP → ℂ[X]) (rec : GLRep g → LP)
    (h2 : DepthZeroCuspidal g) (h3 : Pinned S teich ine rec) (ρ : GLRep g) (hρ : IsSC ρ) (f : (ZMod g)[X])
    (h : Has S ρ.2.ρ f) : ine (rec ρ) = liftPoly teich f := by
  obtain ⟨τ, φ, hs, hinj, heq, he⟩ := exists_simple_of_has S _ f h
  have hφ : (fixK1 ρ.2.ρ).subtype ∘ₗ φ ≠ 0 := fun e => by
    have h0 : ∀ u : τ, u = 0 := fun u => hinj (Subtype.ext (by simpa using LinearMap.congr_fun e u))
    exact id_nonzero τ (by ext u; exact (h0 _).trans (h0 _).symm)
  have hfix : fixK1 ρ.2.ρ ≠ ⊥ := fun e => hφ (LinearMap.ext fun u => (Submodule.eq_bot_iff _).1 e _ (φ u).2)
  refine h3 ρ hρ τ hs (fun b hb hb' u hu => hinj ?_) ⟨_, hφ, fun k w => ?_⟩ f he
  · rw [map_zero]
    exact h2 ρ hρ hfix b hb hb' _ fun x hx => by rw [← heq, hu x hx]
  · simp only [LinearMap.comp_apply, Submodule.subtype_apply, heq, repK_red]

theorem ine_eq_of_has (g : ℕ) [Fact g.Prime] (S : Sys g) (teich : Formalism.CyclotomicNorms.Fbar g → ℂ) (LP : Type) (ine : LP → ℂ[X])
    (rec : GLRep g → LP) (h1 : SupportCompat ine rec) (h2 : DepthZeroCuspidal g) (h3 : Pinned S teich ine rec)
    (π : GLRep g) (hπ : IsIrrRep π.2.ρ) (hs : PRep.IsSmooth π.2.ρ) (f : (ZMod g)[X]) (h : Has S π.2.ρ f) :
    ine (rec π) = ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (teich x)).prod := by
  obtain ⟨L, hL, hsc, he⟩ := h1 π hπ hs
  obtain ⟨fs, hfs, rfl⟩ := GlobalTheory.T.series_eq_prod_of_parabolic_induction_chain g S π L hL f h
  rw [he]
  change _ = liftPoly teich fs.prod
  clear he hL h
  suffices fs.prod.Monic ∧ (L.map fun ρ => ine (rec ρ)).prod = liftPoly teich fs.prod from this.2
  induction hfs with
  | nil => simp [liftPoly_one]
  | @cons ρ f L fs hρ _ ih =>
    obtain ⟨hm, ih⟩ := ih fun ρ' h' => hsc ρ' (List.mem_cons_of_mem _ h')
    refine ⟨by simpa using (Has.monic hρ).mul hm, ?_⟩
    rw [List.map_cons, List.prod_cons, List.prod_cons, liftPoly_mul _ (Has.monic hρ).ne_zero hm.ne_zero, ih,
      ine_eq_of_isSC S teich ine rec h2 h3 ρ (hsc ρ List.mem_cons_self) f hρ]

def TameParam (L : LabelDatum g) {LP : Type} (ine : LP → ℂ[X]) (rec : GLRep g → LP) : Prop :=
  ∀ ρ : GLRep g, IsSC ρ → ∀ (τ : FDRep ℂ (Gn g ρ.1)) (P : (ZMod g)[X]), IsCuspOf L P τ.character →
    Inflates ρ.2.ρ τ → ine (rec ρ) = liftPoly L.teich P

def LabelsCusp (S : Sys g) (L : LabelDatum g) : Prop :=
  ∀ (d : ℕ) (τ : FDRep ℂ (Gn g d)) (P : (ZMod g)[X]), IsCuspOf L P τ.character →
    Representation.asAlgebraHom τ.ρ (S.e d P) ≠ 0

theorem mem_unipRadical_iff {d a : ℕ} (had : a < d) (x : Gn g d) :
    x ∈ FiniteGL.unipRadical (ZMod g) (FiniteGL.twoBlocks d a) ↔
      InPar a (x : Mt g d) ∧ tl a (x : Mt g d) = ((1 : Gn g a) : Mt g a) ∧
        br a (d - a) (x : Mt g d) = ((1 : Gn g (d - a)) : Mt g (d - a)) := by
  rw [FiniteGL.mem_unipRadical]
  simp only [FiniteGL.twoBlocks, Matrix.sub_apply, sub_eq_zero, Units.val_one]
  constructor
  · intro h
    refine ⟨fun i j hj hi => ?_, ?_, ?_⟩
    · rw [h i j (by simp [hj]), Matrix.one_apply_ne (fun e => by subst e; omega)]
    · ext i j
      have hi : (i : ℕ) < d := by omega
      have hj : (j : ℕ) < d := by omega
      simp only [tl, Formalism.MainNotions.ArithmeticCylinders.entN, hi, hj, and_self, dif_pos]
      rw [h _ _ (by simp)]
      simp [Matrix.one_apply, Fin.ext_iff]
    · ext i j
      have hi : a + (i : ℕ) < d := by omega
      have hj : a + (j : ℕ) < d := by omega
      simp only [br, Formalism.MainNotions.ArithmeticCylinders.entN, hi, hj, and_self, dif_pos]
      rw [h _ _ (by simp)]
      simp [Matrix.one_apply, Fin.ext_iff]
  · rintro ⟨h0, h1, h2⟩ i j hij
    by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a
    · have := congrFun (congrFun h1 ⟨i, hi⟩) ⟨j, hj⟩
      simpa [tl, Formalism.MainNotions.ArithmeticCylinders.entN, Matrix.one_apply, Fin.ext_iff] using this
    · simp [hi, hj] at hij
    · rw [h0 i j hj (by omega), Matrix.one_apply_ne (fun e => by subst e; omega)]
    · have := congrFun (congrFun h2 ⟨i - a, by omega⟩) ⟨j - a, by omega⟩
      have ei : a + (i - a) = i := by omega
      have ej : a + (j - a) = j := by omega
      have e : ((i : ℕ) - a = j - a) ↔ (i : ℕ) = j := by omega
      simpa [br, Formalism.MainNotions.ArithmeticCylinders.entN, Matrix.one_apply, Fin.ext_iff, ei, ej, e] using this

theorem isCusp_character {d : ℕ} (hd : 0 < d) (τ : FDRep ℂ (Gn g d)) (hs : Simple τ)
    (hc : FiniteGL.IsCuspidal τ.ρ) : IsCusp τ.character := by
  refine ⟨hd, ⟨τ, hs, fun _ => rfl⟩, fun a h0 had => ?_⟩
  set U := FiniteGL.unipRadical (ZMod g) (FiniteGL.twoBlocks d a)
  have hz : ∑ u : U, τ.ρ u = 0 := by
    refine LinearMap.ext fun v => (FiniteGL.isCuspidal_iff_twoBlocks τ.ρ).1 hc a h0 had _ fun x hx => ?_
    rw [LinearMap.sum_apply, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft (⟨x, hx⟩ : U)) _ _ fun u => ?_
    simp
  have ht := congrArg (LinearMap.trace ℂ τ) hz
  rw [map_sum, map_zero] at ht
  unfold res
  rw [← Finset.sum_filter, Finset.sum_subtype (p := fun x => x ∈ U) _
    (fun x => by rw [mem_unipRadical_iff had]; simp) τ.character]
  exact mul_eq_zero_of_right _ ht

theorem pinned_of_green (S : Sys g) (L : LabelDatum g) {LP : Type} (ine : LP → ℂ[X]) (rec : GLRep g → LP)
    (hG : Green) (hT : TameParam L ine rec) (hS : LabelsCusp S L) : Pinned S L.teich ine rec := by
  intro ρ hρ τ hs hc hi f he
  obtain ⟨t, h1, -, h3⟩ := hG g L ρ.1 hρ.1
  obtain ⟨P, hP, e⟩ := h3 _ (isCusp_character hρ.1 τ hs hc)
  have hP' : IsCuspOf L P τ.character := e ▸ (h1 P hP).1
  have : f = P := by
    by_contra hne
    apply hS _ τ P hP'
    rw [← one_mul (Representation.asAlgebraHom τ.ρ _), ← he, ← map_mul, S.orth _ _ _ hne, map_zero]
  rw [this]
  exact hT ρ hρ τ P hP' hi

theorem ine_eq_of_has_green (S : Sys g) (L : LabelDatum g) (LP : Type) (ine : LP → ℂ[X]) (rec : GLRep g → LP)
    (h1 : SupportCompat ine rec) (h2 : DepthZeroCuspidal g) (hG : Green) (hT : TameParam L ine rec)
    (hS : LabelsCusp S L) (π : GLRep g) (hπ : IsIrrRep π.2.ρ) (hs : PRep.IsSmooth π.2.ρ) (f : (ZMod g)[X])
    (h : Has S π.2.ρ f) : ine (rec π) = ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (L.teich x)).prod :=
  ine_eq_of_has g S L.teich LP ine rec h1 h2 (pinned_of_green S L ine rec hG hT hS) π hπ hs f h

theorem principalCongruenceFixedVectors_le_smoothVectors {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) : fixK1 π ≤ PRep.smoothPart π := by
  intro v hv
  let T : Subgroup (GL (Fin n) ℚ_[g]) :=
    { carrier := {x | π x v = v}
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply] at *
        rw [hy, hx]
      one_mem' := by simp
      inv_mem' := by
        intro x hx
        simp only [Set.mem_ofPred_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul]; simp }
  have ho : IsOpen {x : GL (Fin n) ℚ_[g] | ∀ i j, ‖(x.val - 1) i j‖ < 1} := by
    simp only [Set.ofPred_forall]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_lt ?_ continuous_const
    exact ((Units.continuous_val.sub continuous_const).matrix_elem i j).norm
  refine T.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (ho.mem_nhds (by simp)) fun x hx => ?_)
  let N : Matrix (Fin n) (Fin n) ℤ_[g] := Matrix.of fun i j => ⟨(x.val - 1) i j, (hx i j).le⟩
  have hN : (PadicInt.toZMod (p := g)).mapMatrix N = 0 := by
    ext i j
    have : N i j ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
      exact hx i j
    exact this
  have hM : (PadicInt.toZMod (p := g)).mapMatrix (N + 1) = 1 := by rw [map_add, hN, map_one, zero_add]
  have hd : IsUnit (N + 1).det := by
    by_contra h
    have h1 : (N + 1).det ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [PadicInt.ker_toZMod]; exact h
    rw [RingHom.mem_ker, RingHom.map_det, hM] at h1
    simp at h1
  let k : GL (Fin n) ℤ_[g] := ((Matrix.isUnit_iff_isUnit_det _).2 hd).unit
  have e1 : red g n k = 1 := Units.ext hM
  have e2 : inc g n k = x := by
    refine Units.ext ?_
    change (algebraMap ℤ_[g] ℚ_[g]).mapMatrix (N + 1) = x.val
    rw [map_add, map_one]
    exact (congrArg (· + 1) (show (algebraMap ℤ_[g] ℚ_[g]).mapMatrix N = x.val - 1 from rfl)).trans
      (sub_add_cancel _ _)
  exact e2 ▸ (Model.mem_principalCongruenceFixedVectors_iff π v).1 hv k e1

theorem isSmooth_of_fixK1 {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) ℚ_[g]) V} (hπ : IsIrrRep π) (h : fixK1 π ≠ ⊥) : PRep.IsSmooth π := by
  rcases hπ.2 _ (PRep.smoothPart_stable π) with e | e
  · exact absurd (le_bot_iff.1 (e ▸ principalCongruenceFixedVectors_le_smoothVectors π)) h
  · exact fun v => (e ▸ Submodule.mem_top : v ∈ PRep.smoothPart π)

theorem ine_eq_of_has' (S : Sys g) (teich : Formalism.CyclotomicNorms.Fbar g → ℂ) (LP : Type) (ine : LP → ℂ[X])
    (rec : GLRep g → LP) (h1 : SupportCompat ine rec) (h2 : DepthZeroCuspidal g) (h3 : Pinned S teich ine rec)
    (π : GLRep g) (hπ : IsIrrRep π.2.ρ) (f : (ZMod g)[X]) (h : Has S π.2.ρ f) :
    ine (rec π) = ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (teich x)).prod := by
  refine ine_eq_of_has g S teich LP ine rec h1 h2 h3 π hπ (isSmooth_of_fixK1 hπ fun e => ?_) f h
  obtain ⟨v, hv, hne⟩ := h
  exact hne (by rw [(Submodule.eq_bot_iff _).1 e v hv, map_zero])

theorem isSC_tameRep (χ : (ZMod g)ˣ →* ℂˣ) : IsSC (tameRep χ) ∧ fixK1 (tameRep χ).2.ρ ≠ ⊥ := by
  have hfix : fixK1 (Model.detRep 1 (Model.tame χ)) ≠ ⊥ := fun e =>
    one_ne_zero ((Submodule.eq_bot_iff _).1 e 1 (Model.tame_mem_fixK1 χ 1))
  refine ⟨⟨one_pos, Model.isIrrRep_chRep _, isSmooth_of_fixK1 (Model.isIrrRep_chRep _) hfix, fun v l _ =>
    ⟨{1}, isCompact_singleton, fun (x : GL (Fin 1) ℚ_[g]) _ => ⟨x, ?_, 1, rfl, (mul_one x).symm⟩⟩⟩, hfix⟩
  have hc : ∀ x y : GL (Fin 1) ℚ_[g], y * x = x * y := fun x y => Units.ext (by
    ext i j
    simp [Matrix.mul_apply, Subsingleton.elim i 0, Subsingleton.elim j 0, mul_comm])
  exact Subgroup.mem_center_iff.2 (hc x)

theorem inflates_tameRep (χ : (ZMod g)ˣ →* ℂˣ) :
    Inflates (Model.detRep 1 (Model.tame χ))
      (FDRep.of (Model.chRep (χ.comp (Matrix.GeneralLinearGroup.det (n := Fin 1))))) := by
  refine ⟨LinearMap.id, fun e => one_ne_zero (LinearMap.congr_fun e (1 : ℂ)), fun k (w : ℂ) => ?_⟩
  change Model.chRep _ _ w = Model.chRep _ _ w
  simp [Model.tame_inc]

end GlobalTheory.SerSys.TameGen
