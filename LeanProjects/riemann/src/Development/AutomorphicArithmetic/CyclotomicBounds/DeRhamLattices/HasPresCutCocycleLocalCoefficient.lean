import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstOneMem
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.HasPres
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsLinearMapSpanBaseChangeOfSemilinear
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocMulVec
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases UpperTheory.KN

private theorem cutPres_gen {G O O' LL Q X : Type} [Group G] [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [CommRing O'] [Field LL] [Algebra O' LL] [AddCommGroup Q] [Module O' Q] (f : O →+* O')
    (fK : FractionRing O →+* LL) {a n : ℕ} (N : X → (G →* Matrix (Fin n) (Fin n) O'))
    (actQ : G → Q →ₗ[O'] Q) (x : Fin a → X) (A : G → Fin a → Matrix (Fin n) (Fin n) (FractionRing O))
    (hA : ∀ g j v, ((N (x j) g).map (algebraMap O' LL)).mulVec (fun m => fK (v m)) = fun m => fK ((A g j).mulVec v m))
    (E : Fin a → Fin n → FractionRing O) (Y : Submodule O (Fin a → Fin n → FractionRing O)) (hY : Y.FG)
    (hst : ∀ g, ∀ y ∈ Y, (fun j => (A g j).mulVec (y j)) ∈ Y)
    (hE : ∀ g, (fun j => (A g j).mulVec (E j) - E j) ∈ Y) {Q0 : Type} [AddCommGroup Q0] [Module O Q0] (φ0 : ↥Y →ₗ[O] Q0)
    (θ : Q0 → Q) (act0 : G → Q0 → Q0)
    (hinj : Function.Injective (algebraMap O' LL))
    (hf : ∀ c, fK (algebraMap O (FractionRing O) c) = algebraMap O' LL (f c))
    (hθa : ∀ p q, θ (p + q) = θ p + θ q) (hθs : ∀ (c : O) q, θ (c • q) = f c • θ q)
    (hθe : ∀ g q, θ (act0 g q) = actQ g (θ q))
    (hφ0 : ∀ g (y : ↥Y), φ0 ⟨_, hst g y.1 y.2⟩ = act0 g (φ0 y)) :
    HasPres LL N (Q := Q) (fun g => actQ g) (fun g => θ (φ0 ⟨_, hE g⟩)) := by
  let ψ : ↥Y →+ Q := AddMonoidHom.mk' (fun y => θ (φ0 y)) (fun u v => by rw [map_add, hθa])
  have hψ : ∀ (c : O) (y : ↥Y), ψ (c • y) = f c • ψ y := fun c y => by
    change θ (φ0 (c • y)) = f c • θ (φ0 y)
    rw [map_smul, hθs]
  have heq : ∀ g (y : ↥Y), ψ ⟨_, hst g y.1 y.2⟩ = actQ g (ψ y) := fun g y => by
    change θ (φ0 ⟨_, hst g y.1 y.2⟩) = actQ g (θ (φ0 y))
    rw [hφ0, hθe]
  let ι : (Fin a → Fin n → FractionRing O) → (Fin a → Fin n → LL) := fun y j m => fK (y j m)
  have hι : ι = fun y j m => fK (y j m) := rfl
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥(Submodule.span O' (ι '' (Y : Set _))) →ₗ[O'] Q,
      ∀ y : ↥Y, φ ⟨ι y.1, Submodule.subset_span ⟨y.1, y.2, rfl⟩⟩ = ψ y := by
    have H := UpperTheory.KN.exists_linearMap_span_baseChange_of_semilinear f fK Y ψ hinj hf hY hψ
    exact H
  have hact : ∀ g y, actN LL (fun j => N (x j)) g (ι y) = ι (fun j => (A g j).mulVec (y j)) := by
    intro g y
    funext j
    exact hA g j (y j)
  have hadd : ∀ g u v, actN LL (fun j => N (x j)) g (u + v) =
      actN LL (fun j => N (x j)) g u + actN LL (fun j => N (x j)) g v := by
    intro g u v
    funext j
    simp [actN, Matrix.mulVec_add]
  have hsmul : ∀ g (c : O') u, actN LL (fun j => N (x j)) g (c • u) = c • actN LL (fun j => N (x j)) g u := by
    intro g c u
    funext j
    simp [actN, Matrix.mulVec_smul]
  have hzero : ∀ g, actN LL (fun j => N (x j)) g 0 = 0 := by
    intro g
    funext j
    simp [actN]
  have hst' : ∀ g, ∀ y ∈ Submodule.span O' (ι '' (Y : Set _)),
      actN LL (fun j => N (x j)) g y ∈ Submodule.span O' (ι '' (Y : Set _)) := by
    intro g u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨y, hy, rfl⟩ := hu
      rw [hact]
      exact Submodule.subset_span ⟨_, hst g y hy, rfl⟩
    | zero => rw [hzero]; exact Submodule.zero_mem _
    | add u v _ _ hu hv => rw [hadd]; exact Submodule.add_mem _ hu hv
    | smul c u _ hu => rw [hsmul]; exact Submodule.smul_mem _ c hu
  have hEE : ∀ g, actN LL (fun j => N (x j)) g (ι E) - ι E = ι (fun j => (A g j).mulVec (E j) - E j) := by
    intro g
    rw [hact]
    funext j m
    simp [hι]
  have hE' : ∀ g, actN LL (fun j => N (x j)) g (ι E) - ι E ∈ Submodule.span O' (ι '' (Y : Set _)) := by
    intro g
    rw [hEE]
    exact Submodule.subset_span ⟨_, hE g, rfl⟩
  have hfg : (Submodule.span O' (ι '' (Y : Set _))).FG := by
    obtain ⟨S, hS, hSY⟩ := Submodule.fg_def.1 hY
    refine Submodule.fg_def.2 ⟨ι '' S, hS.image _, le_antisymm (Submodule.span_mono (Set.image_mono ?_)) ?_⟩
    · rw [← hSY]; exact Submodule.subset_span
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨y, hy, rfl⟩
      rw [← hSY] at hy
      change ι y ∈ Submodule.span O' (ι '' S)
      induction hy using Submodule.span_induction with
      | mem u hu => exact Submodule.subset_span ⟨u, hu, rfl⟩
      | zero =>
        have : ι 0 = 0 := by funext j m; simp [hι]
        rw [this]; exact Submodule.zero_mem _
      | add u v _ _ hu hv =>
        have : ι (u + v) = ι u + ι v := by funext j m; simp [hι]
        rw [this]; exact Submodule.add_mem _ hu hv
      | smul c u _ hu =>
        have : ι (c • u) = f c • ι u := by
          funext j m
          change fK (c • u j m) = f c • fK (u j m)
          simp only [Algebra.smul_def, map_mul, hf]
        rw [this]; exact Submodule.smul_mem _ _ hu
  refine ⟨a, x, ι E, _, hfg, hst', hE', φ, ?_, ?_⟩
  · intro g
    let L : (Fin a → Fin n → LL) →ₗ[O'] (Fin a → Fin n → LL) :=
      { toFun := actN LL (fun j => N (x j)) g, map_add' := hadd g, map_smul' := hsmul g }
    have key : φ ∘ₗ L.restrict (hst' g) = actQ g ∘ₗ φ := by
      rw [Submodule.linearMap_eq_iff_of_eq_span _ _ rfl]
      rintro ⟨_, y, hy, rfl⟩
      have h1 := hφ ⟨y, hy⟩
      have h2 := hφ ⟨_, hst g y hy⟩
      have h3 := heq g ⟨y, hy⟩
      rw [LinearMap.comp_apply, LinearMap.comp_apply, h1, ← h3, ← h2]
      congr 1
      exact Subtype.ext (hact g y)
    intro y
    exact LinearMap.congr_fun key y
  · intro g
    have h2 := hφ ⟨_, hE g⟩
    change ψ ⟨_, hE g⟩ = _
    rw [← h2]
    congr 1
    exact Subtype.ext (hEE g).symm

private theorem cutPres_mulVec {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ}
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) (v : Fin k → KK D.nd i) :
    ((locOC C M g).map (algebraMap ↥(OL C.LL) ↥C.LL.1)).mulVec
        (fun m => ((IntermediateField.inclusion C.le).toRingHom.comp (Br.toLLK (D.nbr i w hw))) (v m)) =
      fun m => ((IntermediateField.inclusion C.le).toRingHom.comp (Br.toLLK (D.nbr i w hw)))
        ((mapM (toK D.nd i) M ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd)).mulVec v m) := by
  have h := GlobalTheory.Pass.LocDirect.loc_mulVec i w hw M g v
  funext m
  rw [RingHom.comp_apply, ← congrFun h m, RingHom.map_mulVec]
  rfl

private theorem cutPres_alg {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (c : D.nd.O i) :
    ((IntermediateField.inclusion C.le).toRingHom.comp (Br.toLLK (D.nbr i w hw))) (algebraMap (D.nd.O i) (KK D.nd i) c) =
      algebraMap ↥(OL C.LL) ↥C.LL.1 (((incO C.le).comp (D.nbr i w hw).eO.toRingHom) c) := by
  rw [RingHom.comp_apply, Br.toLLK_alg]
  rfl

private theorem cutPres_smul {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (c : D.nd.O i)
    (q : KOG (D.nd.O i) k) :
    liftQ C.le k (Br.phi (D.nbr i w hw) k (c • q)) =
      ((incO C.le).comp (D.nbr i w hw).eO.toRingHom) c • liftQ C.le k (Br.phi (D.nbr i w hw) k q) := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have h : (fun m => ((IntermediateField.inclusion C.le).toRingHom.comp (Br.toLLK (D.nbr i w hw))) (c • u m)) =
      ((incO C.le).comp (D.nbr i w hw).eO.toRingHom) c •
        (fun m => ((IntermediateField.inclusion C.le).toRingHom.comp (Br.toLLK (D.nbr i w hw))) (u m)) := by
    funext m
    rw [Pi.smul_apply, Algebra.smul_def, Algebra.smul_def, map_mul, cutPres_alg]
  exact congrArg (Submodule.Quotient.mk (p := stdG ↥(OL C.LL) ↥C.LL.1 k)) h

private theorem cutPres_act {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ}
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) (q : KOG (D.nd.O i) k) :
    liftQ C.le k (Br.phi (D.nbr i w hw) k (WKG M ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) q)) =
      actD (latC C (locOC C M)) g (liftQ C.le k (Br.phi (D.nbr i w hw) k q)) := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact congrArg (Submodule.Quotient.mk (p := stdG ↥(OL C.LL) ↥C.LL.1 k)) (cutPres_mulVec C M g u).symm

private theorem cutPres_add {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (p q : KOG (D.nd.O i) k) :
    liftQ C.le k (Br.phi (D.nbr i w hw) k (p + q)) =
      liftQ C.le k (Br.phi (D.nbr i w hw) k p) + liftQ C.le k (Br.phi (D.nbr i w hw) k q) :=
  (congrArg (liftQ C.le k) ((Br.phi (D.nbr i w hw) k).map_add p q)).trans ((liftQ C.le k).map_add _ _)

theorem _root_.UpperTheory.KN.hasPres_cutCocycle_localCoefficient :
    ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
      (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)), ∀ z ∈ cutCoc i w hw r Set.univ M,
      HasPres ↥C.LL.1 (fun x => locOC C (rTwO D.nd i r x)) (Q := (Fin k → ↥C.LL.1) ⧸ stdG ↥(OL C.LL) ↥C.LL.1 k)
        (fun g => actD (latC C (locOC C M)) g) (fun g => liftQ C.le k (z g)) := by
  intro D i r w hw C k M z hz
  obtain ⟨a, x, -, E, Y, hY, hst, hE, φ, hφ, rfl⟩ := hz
  have H := cutPres_gen (Q := (Fin k → ↥C.LL.1) ⧸ stdG ↥(OL C.LL) ↥C.LL.1 k)
    ((incO C.le).comp (D.nbr i w hw).eO.toRingHom)
    ((IntermediateField.inclusion C.le).toRingHom.comp (Br.toLLK (D.nbr i w hw)))
    (fun x => locOC C (rTwO D.nd i r x)) (fun g => actD (latC C (locOC C M)) g) x
    (fun g j => mapM (toK D.nd i) (rTwO D.nd i r (x j)) ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd))
    (fun g j v => cutPres_mulVec C _ g v) E Y hY (fun g => hst _) (fun g => hE _)
    φ (fun q => liftQ C.le k (Br.phi (D.nbr i w hw) k q))
    (fun g => WKG M ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd))
    Subtype.val_injective (cutPres_alg C) (cutPres_add C)
    (cutPres_smul C) (cutPres_act C M) (fun g => hφ _)
  exact H
