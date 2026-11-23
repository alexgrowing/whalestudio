import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtAlong
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackPrj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.BaseChRig

theorem valR_map {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U V : X.Opens} (h : V ≤ U)
    (hV : ⊤ ≤ x ⁻¹ᵁ V) (s : Γ(X, U)) :
    valR x V ((X.presheaf.map (homOfLE h).op).hom s) = valR x U s := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := fun q hq => h (hV hq)
  unfold valR
  rw [dif_pos hV, dif_pos hU, ← Scheme.Hom.map_appLE x hV (homOfLE h).op]
  rfl

theorem valR_app {A : Type} [CommRing A] {X Y : Scheme.{0}} (x : Sp A ⟶ Y) (g : Y ⟶ X) {U : X.Opens}
    (hU : ⊤ ≤ x ⁻¹ᵁ (g ⁻¹ᵁ U)) (s : Γ(X, U)) :
    valR x (g ⁻¹ᵁ U) ((g.app U).hom s) = valR (x ≫ g) U s := by
  have hU' : ⊤ ≤ (x ≫ g) ⁻¹ᵁ U := hU
  unfold valR
  rw [dif_pos hU, dif_pos hU', Scheme.Hom.comp_appLE]
  rfl

theorem valR_spMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {X : Scheme.{0}} (x : Sp A ⟶ X)
    {U : X.Opens} (hU : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) :
    valR (spMap f ≫ x) U s = f (valR x U s) := by
  have hU' : ⊤ ≤ (spMap f ≫ x) ⁻¹ᵁ U := fun q _ => hU (Set.mem_univ _)
  unfold valR
  rw [dif_pos hU, dif_pos hU']
  have e : (spMap f ≫ x).appLE U ⊤ hU' = x.appLE U ⊤ hU ≫ (spMap f).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [e]
  exact congrArg (fun φ => φ.hom ((x.appLE U ⊤ hU).hom s)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))

theorem valR_mul' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U : X.Opens}
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (s t : Γ(X, U)) : valR x U (s * t) = valR x U s * valR x U t := by
  unfold valR
  simp only [dif_pos hU, map_mul]

theorem valR_pow' {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U : X.Opens}
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) (n : ℕ) : valR x U (s ^ n) = valR x U s ^ n := by
  unfold valR
  simp only [dif_pos hU, map_pow]

theorem valR_gen {A : Type} [CommRing A] {X : Scheme.{0}} (L : LB X) (e : Sp A ⟶ X) (r : (L.pull e).Gen)
    (hr : r.IsGen) (j i : L.ι) (hj : ⊤ ≤ e ⁻¹ᵁ L.U j) (hi : ⊤ ≤ e ⁻¹ᵁ L.U i) :
    valR (𝟙 _) _ (r.s fun _ => j).val = valR e _ (L.g j i).val * valR (𝟙 _) _ (r.s fun _ => i).val := by
  have hB : ⊤ ≤ (𝟙 (Sp A)) ⁻¹ᵁ ((L.pull e).U (fun _ => j) ⊓ (L.pull e).U (fun _ => i)) :=
    fun q hq => ⟨Set.mem_iInter.2 fun _ => hj hq, Set.mem_iInter.2 fun _ => hi hq⟩
  have h := congrArg (fun v => valR (𝟙 (Sp A)) _ (Units.val v)) (hr (fun _ => j) (fun _ => i))
  replace h := h.trans (valR_mul' _ hB _ _)
  refine (valR_map _ _ hB _).symm.trans (h.trans (congrArg₂ (· * ·) ?_ (valR_map _ _ hB _)))
  show valR _ _ (Units.val (∏ _k : PUnit, (res _ (pullU e _ (L.g j i))) ^ (1 : ℤ))) = _
  rw [Fintype.prod_unique, zpow_one]
  refine (valR_map _ _ hB _).trans ((valR_app (𝟙 _) e (U := L.U j ⊓ L.U i) (fun q hq => ⟨hj hq, hi hq⟩) _).trans ?_)
  rw [Category.id_comp]

theorem valR_powIso {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X)
    (e : Sp A ⟶ X) (e' : Sp B ⟶ Y) (he : e' ≫ φ = spMap f ≫ e) (n : ℕ) (i : L.ι) (i' : PUnit → L.ι)
    (hj : ⊤ ≤ e ⁻¹ᵁ L.U (i' PUnit.unit)) (hi : ⊤ ≤ e ⁻¹ᵁ L.U i) (hi' : ⊤ ≤ e' ⁻¹ᵁ (L.pull φ).U i') :
    valR e' _ ((BaseCh.powIso L φ n).s (fun _ => i', fun _ _ => i)).val =
      f (valR e _ (L.g (i' PUnit.unit) i).val) ^ n := by
  have h2 : ∀ q, φ (e' q) ∈ L.U i := fun q => by
    show (e' ≫ φ) q ∈ L.U i
    rw [he]; exact hi (Set.mem_univ _)
  have hB : ⊤ ≤ e' ⁻¹ᵁ (LB.div (lbPow (L.pull φ) n) ((lbPow L n).pull φ)).U (fun _ => i', fun _ _ => i) :=
    fun q hq => ⟨Set.mem_iInter.2 fun _ => hi' hq, Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun _ => h2 q⟩
  show valR e' _ (Units.val (res (BaseCh.powIso_le L φ n (fun _ => i', fun _ _ => i))
      (pullU φ _ (L.g (i' PUnit.unit) i)) ^ (n : ℤ))) = _
  rw [zpow_natCast, Units.val_pow_eq_pow_val, valR_pow' _ hB]
  congr 1
  refine (valR_map _ _ hB _).trans ((valR_app e' φ (U := L.U (i' PUnit.unit) ⊓ L.U i)
    (fun q hq => BaseCh.powIso_le L φ n (fun _ => i', fun _ _ => i) (hB hq)) _).trans ?_)
  rw [he]
  exact valR_spMap f e (U := L.U (i' PUnit.unit) ⊓ L.U i) (fun q hq => ⟨hj hq, hi hq⟩) _

theorem powIso_rig : ∀ (K K' : Type) [Field K] [Field K'] (f : K →+* K') (x : KeyIn K) (n : ℕ) (i : x.P.L.ι) (i' : (GlobalTheory.MBLow.BaseCh.key x f).P.L.ι), ⊤ ≤ (eSec x.P.A) ⁻¹ᵁ x.P.L.U i → ⊤ ≤ (eSec (GlobalTheory.MBLow.BaseCh.key x f).P.A) ⁻¹ᵁ (GlobalTheory.MBLow.BaseCh.key x f).P.L.U i' → valR (X := (GlobalTheory.MBLow.BaseCh.key x f).P.A.left) (eSec (GlobalTheory.MBLow.BaseCh.key x f).P.A) _ ((GlobalTheory.MBLow.BaseCh.powIso x.P.L (GlobalTheory.MBLow.BaseCh.prj x f) n).s (fun _ => i', fun _ _ => i)).val * f (valR (X := Sp K) (𝟙 _) _ (x.rig.s fun _ => i).val) ^ n = valR (X := Sp K') (𝟙 _) _ ((GlobalTheory.MBLow.BaseCh.key x f).rig.s fun _ => i').val ^ n := by
  intro K K' _ _ f x n i i' hi hi'
  have he := BaseCh.eSec_prj x f
  have hj : ⊤ ≤ (eSec x.P.A) ⁻¹ᵁ x.P.L.U (i' PUnit.unit) := by
    intro q _
    have h1 : (eSec (BaseCh.pol x f).A ≫ BaseCh.prj x f) (default : Sp K') ∈ x.P.L.U (i' PUnit.unit) :=
      Set.mem_iInter.1 (hi' (Set.mem_univ (default : Sp K'))) PUnit.unit
    rw [he] at h1
    have h2 : (q : Sp K) = spMap f (default : Sp K') := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [h2]
    exact h1
  have a := valR_powIso f x.P.L (BaseCh.prj x f) (eSec x.P.A) (eSec (BaseCh.pol x f).A) he n i i' hj hi hi'
  have b := valR_gen x.P.L (eSec x.P.A) x.rig x.rig_gen (i' PUnit.unit) i hj hi
  have hB : ⊤ ≤ (𝟙 (Sp K')) ⁻¹ᵁ ((BaseCh.pol x f).L.pull (eSec (BaseCh.pol x f).A)).U (fun _ => i') :=
    fun q hq => Set.mem_iInter.2 fun _ => hi' hq
  have hC : ⊤ ≤ (𝟙 (Sp K)) ⁻¹ᵁ (x.P.L.pull (eSec x.P.A)).U (fun _ => i' PUnit.unit) :=
    fun q hq => Set.mem_iInter.2 fun _ => hj hq
  have c : valR (X := Sp K') (𝟙 _) _ ((BaseCh.key x f).rig.s fun _ => i').val =
      f (valR (X := Sp K) (𝟙 _) _ (x.rig.s fun _ => i' PUnit.unit).val) := by
    refine (valR_map (𝟙 (Sp K')) _ hB _).trans ((valR_app (𝟙 (Sp K')) (spMap f)
      (fun q _ => hC (Set.mem_univ _)) _).trans ?_)
    rw [Category.id_comp, ← Category.comp_id (spMap f)]
    exact valR_spMap f (𝟙 _) hC _
  rw [c]
  refine (congrArg (· * _) a).trans ?_
  rw [← mul_pow, ← map_mul]
  exact congrArg (fun t => f t ^ n) b.symm

end GlobalTheory.MBLow.BaseChRig
