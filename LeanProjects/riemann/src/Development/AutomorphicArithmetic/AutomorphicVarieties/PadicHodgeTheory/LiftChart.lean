import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsFirstOrderDeformationOfRZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SmoothCompl
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.GradedChart
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsLiftFactorCompactSubalgebra
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.HomExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PtCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.LiftGrading
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.DerHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.DerExtend
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

private theorem coeff_single_mul {E σ : Type} [CommRing E] (i : σ) (f g : MvPowerSeries σ E) :
    MvPowerSeries.coeff (Finsupp.single i 1) (f * g) =
      MvPowerSeries.constantCoeff f * MvPowerSeries.coeff (Finsupp.single i 1) g +
      MvPowerSeries.constantCoeff g * MvPowerSeries.coeff (Finsupp.single i 1) f := by
  classical
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  simp [Finset.Nat.antidiagonal_succ, mul_comm]

private theorem hasWeight_of_generators {O R X Q : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (W : WPres O X R) (h : W.HasOrigin) [AddCommGroup Q] [Module O Q] (D : R →ₗ[O] Q)
    (hD : D ∈ PtDer (W.origin h) Q) (j : X) (hz : ∀ s, W.wt s ≠ j → D (W.z s) = 0) : HasWt W.part j D := by
  classical
  let W' := WPres.free O W.wt
  have h' : W'.HasOrigin := fun f hf => by
    have : f = 0 := hf
    rw [this, map_zero]
  have ho : ∀ f, W'.origin h' f = MvPowerSeries.constantCoeff f := fun f => W'.origin_π h' f
  let D' : MvPowerSeries W.σ O →ₗ[O] Q := D ∘ₗ W.π.toLinearMap -
    ∑ s, (MvPowerSeries.coeff (Finsupp.single s 1) : MvPowerSeries W.σ O →ₗ[O] O).smulRight (D (W.z s))
  have hD' : ∀ f, D' f = D (W.π f) - ∑ s, MvPowerSeries.coeff (Finsupp.single s 1) f • D (W.z s) := fun f => by
    simp [D']
  have h0 := (der_extend O _ X W' h' Q).2 D' (fun f g => by
    have h1 : D (W.π f * W.π g) = W.origin h (W.π f) • D (W.π g) + W.origin h (W.π g) • D (W.π f) := hD _ _
    rw [hD', hD', hD', ho, ho, map_mul, h1, W.origin_π, W.origin_π]
    simp only [coeff_single_mul, add_smul, mul_smul, Finset.sum_add_distrib, smul_sub, Finset.smul_sum]
    abel) (fun (s : W.σ) => by
    show D' (MvPowerSeries.X s) = 0
    rw [hD']
    simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj, WPres.z])
  rintro i hi _ ⟨f, hf, rfl⟩
  have h1 := hD' f
  rw [h0, LinearMap.zero_apply, eq_comm, sub_eq_zero] at h1
  refine h1.trans (Finset.sum_eq_zero fun s _ => ?_)
  by_cases hs : W.wt s = j
  · rw [hf (Finsupp.single s 1) (by simpa [Finsupp.weight_single, hs] using hi.symm), zero_smul]
  · rw [hz s hs, smul_zero]

private theorem origin_eq {O R X : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing R] [Algebra O R] [AddCommGroup X] (W : WPres O X R) (x : R →ₐ[O] O)
    (hx : ∀ s, x (W.z s) = 0) : ∃ h : W.HasOrigin, W.origin h = x := by
  have key : ∀ f, x (W.π f) = MvPowerSeries.constantCoeff f := by
    let F : MvPowerSeries W.σ O →ₐ[O] O :=
      { (MvPowerSeries.constantCoeff : MvPowerSeries W.σ O →+* O) with
        commutes' := fun a => by simp [MvPowerSeries.algebraMap_apply] }
    have := (co_ev O O O W.σ (AlgHom.id O O) 0 (fun _ => zero_mem _)).unique (y₁ := x.comp W.π) (y₂ := F)
      ⟨fun a => (x.comp W.π).commutes a, hx⟩ ⟨fun a => F.commutes a, fun s => MvPowerSeries.constantCoeff_X s⟩
    exact fun f => DFunLike.congr_fun this f
  refine ⟨fun f hf => by rw [← key, hf, map_zero], AlgHom.ext fun a => ?_⟩
  obtain ⟨f, rfl⟩ := W.surj a
  exact (W.origin_π _ f).trans (key f).symm

private theorem qcont_lin {l : ℕ} [Fact l.Prime] {V W X : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [AddCommGroup W] [Module ℚ_[l] W] [TopologicalSpace X] {φ : X → V} (hφ : QCont l φ) (ψ : V →ₗ[ℚ_[l]] W) :
    QCont l fun g => ψ (φ g) := by
  letI := moduleTopology ℚ_[l] V
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  letI := moduleTopology ℚ_[l] W
  haveI : IsModuleTopology ℚ_[l] W := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd ℚ_[l] W
  exact (IsModuleTopology.continuous_of_linearMap ψ).comp hφ

private theorem qcont_add {l : ℕ} [Fact l.Prime] {V X : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [TopologicalSpace X] {φ ψ : X → V} (hφ : QCont l φ) (hψ : QCont l ψ) : QCont l fun g => φ g + ψ g := by
  letI := moduleTopology ℚ_[l] V
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd ℚ_[l] V
  exact Continuous.add hφ hψ

private theorem qcont_dual {l : ℕ} [Fact l.Prime] {X E : Type} [TopologicalSpace X] [Field E] [Algebra ℚ_[l] E]
    (f : X → DualNumber E) (h1 : QCont l fun x => (f x).fst) (h2 : QCont l fun x => (f x).snd) : QCont l f := by
  have e : f = fun x => ((TrivSqZeroExt.inlAlgHom ℚ_[l] E E).toLinearMap (f x).fst) +
      (((TrivSqZeroExt.inrHom E E).restrictScalars ℚ_[l]) (f x).snd) :=
    funext fun x => (TrivSqZeroExt.inl_fst_add_inr_snd_eq _).symm
  rw [e]
  exact qcont_add (qcont_lin h1 _) (qcont_lin h2 _)

theorem UpperTheory.V.Loc.liftChart :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] {Γ ι : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O)) {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (w : ι → X) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ : Lift O rbar R) (Q : ∀ (B : Type) [CommRing B] [Algebra O B], (Γ →* Matrix ι ι B) → Prop),
    (∀ (B B' : Type) [CommRing B] [Algebra O B] [CommRing B'] [Algebra O B'] (f : B →ₐ[O] B') (r : Γ →* Matrix ι ι B), (Q B r → Q B' (mapRep (f : B →+* B') r)) ∧ (Function.Injective f → Q B' (mapRep (f : B →+* B') r) → Q B r)) →
    Represents (fun R' _ _ _ r => Q R' r.hom) ρ → ρ.TStable w →
    ∀ ρ₀ : Lift O rbar O, Q O ρ₀.hom → (∀ g a b, w a ≠ w b → ρ₀.hom g a b = 0) →
    (∀ (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (B' : Type) [CommRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [Algebra O B'] [Algebra ℤ_[l] B'] [IsScalarTower ℤ_[l] O B'] [IsScalarTower ℤ_[l] ℚ_[l] B'] [Algebra E B'] [IsScalarTower O E B'] [IsScalarTower ℚ_[l] E B'] (π' : B' →ₐ[E] E) (hπ' : ∀ a, π' a = 0 → IsNilpotent a) (p : B →ₐ[E] B'), Function.Surjective p → π'.comp p = π → ∀ r' : Γ →* Matrix ι ι B', mapRep (π' : B' →+* E) r' = mapRep (algebraMap O E) ρ₀.hom → (∀ a b, QCont l fun g => r' g a b) → Q B' r' → ∃ r : Γ →* Matrix ι ι B, (∀ a b, QCont l fun g => r g a b) ∧ Q B r ∧ mapRep (p : B →+* B') r = r') →
    ∃ (x : R →ₐ[O] O) (P : Ideal R) (n : ℕ) (u : Fin n → X) (φ : R →ₐ[O] MvPowerSeries (Fin n) E), ρ.map x = ρ₀ ∧ UpperTheory.V.Loc.IsCompl P x φ ∧ (∃ y, x y ≠ 0 ∧ ∀ a ∈ P, y * a = 0) ∧ (∀ g a b, φ (ρ.hom g a b) ∈ wtPart E u (w a - w b)) ∧
      ∀ j, ∃ S : Submodule E (Γ → Matrix ι ι E), Nat.card {i // u i = j} = finrank E ↥S ∧ ∀ s, s ∈ S ↔ (∃ r' : Γ →* Matrix ι ι (DualNumber E), (∀ g a b, r' g a b = ⟨algebraMap O E (ρ₀.hom g a b), s g a b⟩) ∧ Q (DualNumber E) r') ∧ (∀ a b, QCont l fun g => s g a b) ∧ ∀ g a b, w a - w b ≠ j → s g a b = 0 := by
  intro l _ O _ _ _ _ _ _ _ Γ ι _ _ _ _ _ _ rbar X _ _ _ w E _ _ _ _ _ _ _ _ R _ _ _ ρ Q hQ hrep hst ρ₀ hQ0 hd hlift
  have hgen : ρ.Generates := fun R' _ _ _ f f' h =>
    ((hrep R').2 _ ((hrep R').1 f')).unique h rfl
  have hQρ : Q R ρ.hom := (hrep R).1 (AlgHom.id O R)
  obtain ⟨x, hx, -⟩ := (hrep O).2 ρ₀ hQ0
  have hxe : ∀ g a b, x (ρ.hom g a b) = ρ₀.hom g a b := fun g a b => by rw [← hx]; rfl
  have hpt : ∀ (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B]
      [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B]
      [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (r : Γ →* Matrix ι ι B),
      (∀ g a b, π (r g a b) = algebraMap O E (ρ₀.hom g a b)) → (∀ a b, QCont l fun g => r g a b) → Q B r →
      ∃ f : R →ₐ[O] B, ∀ g a b, f (ρ.hom g a b) = r g a b := by
    intro B _ _ _ _ _ _ _ _ _ _ π hπ r h1 h2 h3
    obtain ⟨C, hC, ρ', hρ'⟩ := exists_lift_factor_compact_subalgebra (l := l) rbar R ρ E B π hπ ((Algebra.ofId O E).comp x) r
      (fun g a b => by rw [h1, ← hxe]; rfl) h2
    have e : mapRep (C.val : C →+* B) ρ'.hom = r := MonoidHom.ext fun g => Matrix.ext fun a b => hρ' g a b
    obtain ⟨f, hf, -⟩ := (hrep C).2 ρ' ((hQ C B C.val ρ'.hom).2 Subtype.val_injective (e ▸ h3))
    refine ⟨C.val.comp f, fun g a b => ?_⟩
    rw [← hρ', ← hf]
    rfl
  have hc : ∀ (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B]
      [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (f : R →ₐ[O] B) a b,
      QCont l fun g => f (ρ.hom g a b) := fun B _ _ _ _ _ _ _ f a b =>
    (ptCont (l := l) R B f).1 Γ _ (ρ.cont a b)
  obtain ⟨n, P, φ₀, hφ₀, -, ⟨y, hy, hyP⟩, -⟩ := smoothCompl (l := l) E R ⊥ x bot_le (by
    intro B _ _ _ _ _ _ _ _ _ _ π hπ B' _ _ _ _ _ _ _ _ _ _ π' hπ' p hp hpc f' _ hf'
    obtain ⟨r, h1, h2, h3⟩ := hlift B π hπ B' π' hπ' p hp hpc (mapRep (f' : R →+* B') ρ.hom)
      (MonoidHom.ext fun g => Matrix.ext fun a b => (hf' _).trans (congrArg _ (hxe g a b)))
      (hc B' f') ((hQ R B' f' _).1 hQρ)
    have h4 : ∀ g a b, p (r g a b) = f' (ρ.hom g a b) := fun g a b =>
      congrFun (congrFun (DFunLike.congr_fun h3 g) a) b
    obtain ⟨f, hf⟩ := hpt B π hπ r (fun g a b => by rw [← hpc, AlgHom.comp_apply, h4, hf', hxe]) h1 h2
    have := homExt (l := l) rbar R ρ hgen B' ((p.restrictScalars O).comp f) f' fun g a b => by
      rw [← h4, ← hf]; rfl
    exact ⟨f, bot_le, fun a => DFunLike.congr_fun this a⟩)
  obtain ⟨W, hW, hWz⟩ := lift_grading O X Γ ι rbar w R ρ (fun g => ρ₀.hom g)
    (fun g a b => by rw [← ρ₀.red]; exact ((res O O).commutes _).symm) hd hgen hst
  obtain ⟨h, rfl⟩ := origin_eq W x fun s => by
    obtain ⟨g, a, b, e, -⟩ := hWz s
    rw [e, map_sub, hxe, AlgHom.commutes]
    exact sub_self _
  obtain ⟨u, φ, hφ, hφw, hu⟩ := gradedChart (l := l) E R W h P φ₀ hφ₀ ⟨y, hy, hyP⟩
  refine ⟨_, P, n, u, φ, hx, hφ, ⟨y, hy, hyP⟩, fun g a b => hφw _ _ (hW g a b), fun j => ?_⟩
  haveI : Module.Finite E (DualNumber E) := inferInstanceAs (Module.Finite E (E × E))
  haveI : Module.Finite ℚ_[l] (DualNumber E) := inferInstanceAs (Module.Finite ℚ_[l] (E × E))
  let ev : (R →ₗ[O] E) →ₗ[E] (Γ → Matrix ι ι E) :=
    { toFun := fun δ g => Matrix.of fun a b => δ (ρ.hom g a b)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : ∀ δ g a b, ev δ g a b = δ (ρ.hom g a b) := fun _ _ _ _ => rfl
  have hder : ∀ D : R → E, (∃ D' ∈ PtDer ((Algebra.ofId O E).comp (W.origin h)) E, ⇑D' = D) ↔
      ∃ y : R →ₐ[O] DualNumber E, ∀ f, (y f).fst = algebraMap O E (W.origin h f) ∧ (y f).snd = D f := by
    letI : Module Oᵐᵒᵖ E := Module.compHom E (RingEquiv.toOpposite O).symm.toRingHom
    haveI : IsCentralScalar O E := ⟨fun _ _ => rfl⟩
    exact der_hom O R E E ((Algebra.ofId O E).comp (W.origin h))
  have hO : ∀ δ ∈ PtDer ((Algebra.ofId O E).comp (W.origin h)) E, δ ∈ PtDer (W.origin h) E := fun δ hδ f g => by
    rw [hδ f g]
    simp [Algebra.smul_def]
  have hz : ∀ δ ∈ PtDer (W.origin h) E, ∀ g a b c, δ (ρ.hom g a b - algebraMap O R c) = δ (ρ.hom g a b) := by
    intro δ hδ g a b c
    have h1 : δ (1 * 1) = W.origin h 1 • δ 1 + W.origin h 1 • δ 1 := hδ 1 1
    rw [mul_one, map_one (W.origin h), one_smul, left_eq_add] at h1
    rw [map_sub, Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero, sub_zero]
  refine ⟨(wtDer W.part (W.origin h) E j).map ev, (hu j).trans ?_, fun s => ⟨?_, ?_⟩⟩
  · classical
    rw [← Submodule.range_subtype (wtDer W.part (W.origin h) E j), ← LinearMap.range_comp, Submodule.range_subtype,
      LinearMap.finrank_range_of_inj]
    rw [injective_iff_map_eq_zero]
    intro δ hδ
    refine Subtype.ext ((der_extend O R X W h E).2 δ.1 (hO _ δ.2.1) fun s => ?_)
    obtain ⟨g, a, b, e, -⟩ := hWz s
    rw [e, hz _ (hO _ δ.2.1)]
    exact congrFun (congrFun (congrFun hδ g) a) b
  · rintro ⟨δ, ⟨h1, h2⟩, rfl⟩
    obtain ⟨F, hF⟩ := (hder δ).1 ⟨δ, h1, rfl⟩
    refine ⟨⟨mapRep (F : R →+* DualNumber E) ρ.hom, fun g a b => TrivSqZeroExt.ext ?_ (hF _).2,
      (hQ R _ F _).1 hQρ⟩, fun a b => ?_, fun g a b hab => h2 _ hab _ (hW g a b)⟩
    · exact (hF _).1.trans (congrArg (algebraMap O E) (hxe g a b))
    · have := qcont_lin (hc (DualNumber E) F a b) (LinearMap.snd ℚ_[l] E E)
      simp only [hev, ← (hF _).2]
      exact this
  · rintro ⟨⟨r', h1, h2⟩, h3, h4⟩
    obtain ⟨F, hF⟩ := hpt (DualNumber E) (TrivSqZeroExt.fstHom E E E)
      (fun a ha => TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst.2 (by rw [show a.fst = 0 from ha]; exact IsNilpotent.zero))
      r' (fun g a b => by rw [h1]; rfl) (fun a b => qcont_dual _ (by
        simp only [h1, ← hxe]
        exact hc E ((Algebra.ofId O E).comp (W.origin h)) a b) (by
        simp only [h1]
        exact h3 a b)) h2
    have hfst := homExt (l := l) rbar R ρ hgen E (((TrivSqZeroExt.fstHom E E E).restrictScalars O).comp F)
      ((Algebra.ofId O E).comp (W.origin h)) fun g a b => by
        show (F _).fst = algebraMap O E (W.origin h _)
        rw [hF, h1, hxe]
        rfl
    obtain ⟨δ, hδ, e⟩ := (hder fun f => (F f).snd).2 ⟨F, fun f => ⟨DFunLike.congr_fun hfst f, rfl⟩⟩
    have he : ∀ g a b, δ (ρ.hom g a b) = s g a b := fun g a b => by
      rw [e]
      show (F _).snd = _
      rw [hF, h1]
      rfl
    refine ⟨δ, ⟨hδ, hasWeight_of_generators W h δ (hO _ hδ) j fun t ht => ?_⟩, funext fun g => Matrix.ext (he g)⟩
    obtain ⟨g, a, b, e1, e2⟩ := hWz t
    rw [e1, hz _ (hO _ hδ), he, h4 g a b (e2 ▸ ht)]
