import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsValuesLineFibre
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.TwoFrames

theorem valR_eq_valAt' {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) : valR x U f = valAt' x U f := by
  unfold valR valAt' valAt
  congr

theorem map_map {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V) (f : Γ(X, U)) :
    (X.presheaf.map (homOfLE k).op).hom ((X.presheaf.map (homOfLE h).op).hom f) =
      (X.presheaf.map (homOfLE (k.trans h)).op).hom f := by
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

theorem exists_sec_of_pow_one {Z Z' : Scheme.{0}} {L : LB Z} {p : Z' ⟶ Z} (σ : SecP L p 1) :
    ∃ s : (L.pull p).Sec, ∀ (j : L.ι) (x : Sp ℂ ⟶ Z'), ⊤ ≤ (x ≫ p) ⁻¹ᵁ L.U j →
      valAt' x ((L.pull p).U (fun _ => j)) (s.f (fun _ => j)) = ArcPts.sval σ x j := by
  have le : ∀ J : PUnit → L.ι, (L.pull p).U J ≤ LB.wchart L (fun _ : Fin 1 => p) (fun _ => J PUnit.unit) :=
    fun J y hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy PUnit.unit
  refine ⟨⟨fun J => (Z'.presheaf.map (homOfLE (le J)).op).hom (σ.f (fun _ => J PUnit.unit)), fun J J' => ?_⟩,
    fun j x hx => ?_⟩
  · have h := congrArg (Z'.presheaf.map (homOfLE (inf_le_inf (le J) (le J'))).op).hom
      (σ.compat (fun _ => J PUnit.unit) (fun _ => J' PUnit.unit))
    refine ((map_map _ _ _).trans (map_map _ _ _).symm).trans (h.trans ((map_mul _ _ _).trans ?_))
    refine congrArg₂ (· * ·) ?_ ((map_map _ _ _).trans (map_map _ _ _).symm)
    simp only [LB.LinComb, Finset.univ_unique, Finset.prod_singleton, Nat.cast_one, zpow_one]
    refine (map_map _ _ _).trans ?_
    symm
    refine Eq.trans (congrArg Units.val (?_ : (L.pull p).g J J' = res (le_inf (inf_le_left.trans
      (LB.wchart_le L _ J PUnit.unit)) (inf_le_right.trans (LB.wchart_le L _ J' PUnit.unit)))
      (pullU p _ (L.g (J PUnit.unit) (J' PUnit.unit))))) rfl
    show ∏ k : PUnit, _ = _
    have hp : ∀ {G : Type} [CommGroup G] (x : G), ∏ _k : PUnit.{1}, x ^ (1 : ℤ) = x := fun x => by simp
    exact hp _
  · refine Eq.trans ?_ (valR_eq_valAt' x _ _).symm
    exact GlobalTheory.valAt'_map x _ _ (fun q hq => mem_pull.2 ((top_le_preimage_comp _ _ _).1 hx hq))

theorem two_frames : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (A : AnArc (𝓞 E)) lin cst (w : ℂ) (y₀ : Sp ℂ ⟶ Xo.X) (π : A.V → (Over.mk y₀ ⟶ Xo.univ.t.G)) fr (g : ℕ) (h : A.V ≃L[ℂ] (Fin g → ℂ)) (e : (Fin g → ℂ) → (Sp ℂ ⟶ Xo.univ.t.G.left)) (ϑ : (Fin g → ℂ) → ℂ) fr', IsFibAt A Xo.univ.t lin cst w y₀ π fr → (∀ v, e (h v) = (π v).left) → IsThetaFrameAt Xo.univ.t.PP y₀ e ϑ fr' → (∃ z, ϑ z ≠ 0) → ∀ th ∈ A.Theta 1 0, (∃ v, A.Sum 1 0 th w v ≠ 0) → ∃ (lam : ℂ) (f : A.V → ℂ), lam ≠ 0 ∧ Differentiable ℂ f ∧ (∀ v, f v ≠ 0) ∧ f 0 = 1 ∧ (∀ v j, ⊤ ≤ (π v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr' j (h v) = f v * fr j v) ∧ ∀ v, A.Sum 1 0 th w v = lam * ϑ (h v) * f v := by
  intro hL _ E _ _ _ H _ D l Xo A lin cst w y₀ π fr g h e ϑ fr' hF he hT hϑ th hth hS
  obtain ⟨d', n', c', r', s', hs'⟩ := hT
  have ch : ∀ v, ∃ j, ⊤ ≤ (π v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun v => by
    obtain ⟨j, hj⟩ := exists_chart Xo.univ.t.PP.isLB ((π v).left (default : PrimeSpectrum ℂ))
    exact ⟨j, (top_le_preimage_iff_mem _ _).2 hj⟩
  choose J hJ using ch
  have n : ∀ v j, ⊤ ≤ (π v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j v ≠ 0 := fun v j hj => ((hF.frm v).1 j hj).ne_zero
  have key : ∀ v j, ⊤ ≤ (π v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr' j (h v) = fr' (J v) (h v) / fr (J v) v * fr j v := by
    intro v j hj
    have hi := (top_le_preimage_inf _ _ _).2 ⟨hj, hJ v⟩
    have a := (hF.frm v).2 j (J v) hi
    have b := c' j (J v) (h v) (by rw [he]; exact hi)
    rw [he] at b
    rw [valR_eq_valAt'] at a
    beta_reduce at a
    have := n v _ (hJ v)
    rw [b, a]
    field_simp
  obtain ⟨σ, hσ⟩ := hF.sec th hth
  obtain ⟨s, hs⟩ := exists_sec_of_pow_one σ
  obtain ⟨u, hu⟩ := ThetaFamily.exists_values_line_fibre hL.globalSectionsRank Xo.univ y₀
  obtain ⟨a, ha⟩ := hu s
  obtain ⟨a', ha'⟩ := hu s'
  have f1 : ∀ v, fib (π v) ≫ pullback.fst _ _ = (π v).left := fun v => pullback.lift_fst _ _ _
  have f2 : ∀ v, fib (π v) ≫ pullback.snd _ _ = 𝟙 _ := fun v => pullback.lift_snd _ _ _
  have m : ∀ v, ⊤ ≤ (fib (π v) ≫ pullback.fst _ _) ⁻¹ᵁ Xo.univ.t.PP.L.U (J v) := fun v => by
    rw [f1]; exact hJ v
  have m' : ∀ v, ⊤ ≤ fib (π v) ⁻¹ᵁ (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom y₀)).U (fun _ => J v) :=
    fun v q hq => mem_pull.2 ((top_le_preimage_comp _ _ _).1 (m v) hq)
  have e1 : ∀ v, A.Sum 1 0 th w v * fr (J v) v = a * u (fun _ => J v) (fib (π v)) := fun v => by
    rw [← ha _ _ (f2 v) (m' v), hs _ _ (m v), hσ v _ (m v), pow_one]
  have e2 : ∀ v, ϑ (h v) * fr' (J v) (h v) = a' * u (fun _ => J v) (fib (π v)) := fun v => by
    rw [← ha' _ _ (f2 v) (m' v),
      hs' _ (h v) _ ((f1 v).trans (he v).symm) (f2 v) (by rw [he]; exact hJ v)]
  have n'' : ∀ v, fr' (J v) (h v) ≠ 0 := fun v => n' _ _ (by rw [he]; exact hJ v)
  have a0 : a ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := hS
    exact mul_ne_zero hv (n v _ (hJ v)) ((e1 v).trans (zero_mul _))
  have a0' : a' ≠ 0 := by
    rintro rfl
    obtain ⟨z, hz⟩ := hϑ
    obtain ⟨v, rfl⟩ := h.surjective z
    exact mul_ne_zero hz (n'' v) ((e2 v).trans (zero_mul _))
  refine ⟨a / a', fun v => fr' (J v) (h v) / fr (J v) v, div_ne_zero a0 a0', fun v₀ => ?_,
    fun v => div_ne_zero (n'' v) (n v _ (hJ v)), ?_, key, fun v => ?_⟩
  · have op : IsOpen {v | ⊤ ≤ (π v).left ⁻¹ᵁ Xo.univ.t.PP.L.U (J v₀)} := by
      simpa using (hF.hol (Xo.univ.t.PP.L.U (J v₀)) 0).1
    have nh := op.mem_nhds (hJ v₀)
    have d1 : DifferentiableOn ℂ (fun v => fr' (J v₀) (h v))
        {v | ⊤ ≤ (π v).left ⁻¹ᵁ Xo.univ.t.PP.L.U (J v₀)} :=
      (d' (J v₀)).comp h.differentiable.differentiableOn fun v hv => by
        show ⊤ ≤ e (h v) ⁻¹ᵁ _
        rw [he]; exact hv
    have d2 := ((d1.mul ((hF.fr_hol (J v₀)).inv fun v hv => n v _ hv)).differentiableAt nh)
    refine d2.congr_of_eventuallyEq (Filter.mem_of_superset nh fun v hv => ?_)
    show fr' (J v) (h v) / fr (J v) v = fr' (J v₀) (h v) * (fr (J v₀) v)⁻¹
    rw [key v _ hv, mul_inv_cancel_right₀ (n v _ hv)]
  · show fr' (J 0) (h 0) / fr (J 0) 0 = 1
    have h0 : e 0 = (π 0).left := by rw [← he, map_zero]
    rw [div_eq_one_iff_eq (n 0 _ (hJ 0)), map_zero, r' _ (by rw [h0]; exact hJ 0), hF.rig _ (hJ 0)]
  · have := n v _ (hJ v)
    have b1 := e1 v
    have b2 := e2 v
    field_simp
    linear_combination a' * b1 - a * b2

end GlobalTheory.TwoFrames
