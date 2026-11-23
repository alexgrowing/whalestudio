import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyUniformisationFibreTheta
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDerivAt0CompLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingRiemannForm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalBundlePairingCompatiblePullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusPointsSubsetHolPeriodicOneParamSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialKernelsIsHolomorphicLatticeFamily
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLiftOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FibExpAb

theorem span_and_rank {g n : ℕ} {ρ : Type} [Fintype ρ] (K : AddSubgroup (Fin g → ℂ)) (hK : (K : Set (Fin g → ℂ)).Countable)
    (p : (Fin g → ℂ) →ₗ[ℂ] (Fin n → ℂ)) (hp : Function.Surjective p) (L : Submodule ℤ (Fin n → ℂ))
    [DiscreteTopology L] (hL : Submodule.span ℝ (L : Set (Fin n → ℂ)) = ⊤) (emb : (ρ → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h₁ : ∀ w, p w ∈ L ↔ ∃ s, w - emb s ∈ K)
    (h₂ : ∀ s, emb s ∈ K ↔ ∀ j, ∃ a : ℤ, s j = a * (2 * Real.pi * Complex.I)) :
    Submodule.span ℝ (p '' (K : Set (Fin g → ℂ))) = ⊤ ∧
      Module.finrank ℝ (Submodule.span ℝ (K : Set (Fin g → ℂ))) + Module.finrank ℂ (LinearMap.ker p) ≤ 2 * g := by
  classical
  have : IsZLattice ℝ L := ⟨hL⟩
  have := ZLattice.module_finite ℝ L
  have := ZLattice.module_free ℝ L
  have hLc : (L : Set (Fin n → ℂ)).Countable := by
    exact Set.countable_coe_iff.1 (TopologicalSpace.separableSpace_iff_countable.1 (inferInstanceAs (TopologicalSpace.SeparableSpace L)))
  have hpe : ∀ s, p (emb s) = 0 := fun s => FibreUnif.eq_zero_of_smul_mem_countable hLc fun c => by
    rw [← map_smul, ← map_smul]
    exact (h₁ _).2 ⟨c • s, by simp⟩
  have hlift : ∀ l ∈ L, ∃ v ∈ K, p v = l := fun l hl => by
    obtain ⟨w, rfl⟩ := hp l
    obtain ⟨s, hs⟩ := (h₁ w).1 hl
    exact ⟨_, hs, by rw [map_sub, hpe, sub_zero]⟩
  have hinj : Function.Injective emb := by
    refine (injective_iff_map_eq_zero emb).2 fun s hs => ?_
    refine FibreUnif.eq_zero_of_smul_mem_countable
      (Set.countable_range fun a : ρ → ℤ => fun j => (a j : ℂ) * (2 * Real.pi * Complex.I)) fun c => ?_
    choose a ha using (h₂ (c • s)).1 (by rw [map_smul, hs, smul_zero]; exact K.zero_mem)
    exact ⟨a, funext fun j => (ha j).symm⟩
  have hker : LinearMap.ker p = LinearMap.range emb := by
    refine le_antisymm (fun w hw => ?_) ?_
    · rw [← Submodule.Quotient.mk_eq_zero]
      refine FibreUnif.eq_zero_of_smul_mem_countable (hK.image (LinearMap.range emb).mkQ) fun c => ?_
      obtain ⟨s, hs⟩ := (h₁ (c • w)).1 (by rw [map_smul, LinearMap.mem_ker.1 hw, smul_zero]; exact L.zero_mem)
      refine ⟨_, hs, ?_⟩
      rw [map_sub, map_smul, show (LinearMap.range emb).mkQ (emb s) = 0 from
        (Submodule.Quotient.mk_eq_zero _).2 ⟨s, rfl⟩, sub_zero]
      rfl
    · rintro _ ⟨s, rfl⟩
      exact hpe s
  have hr : Module.finrank ℂ (LinearMap.ker p) = Fintype.card ρ := by
    rw [hker, LinearMap.finrank_range_of_inj hinj]
    simp
  have hg : n + Fintype.card ρ = g := by
    have := p.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.2 hp, hr] at this
    simpa using this
  refine ⟨top_le_iff.1 (hL ▸ Submodule.span_mono fun l hl => hlift l hl), ?_⟩
  let b := Module.finBasis ℤ L
  have hb : Module.finrank ℤ L = 2 * n := by
    rw [ZLattice.rank ℝ L, Module.finrank_pi_fintype]
    simp [mul_comm]
  choose lam hlam hpl using fun j => hlift (b j) (b j).2
  let f : Fin (Module.finrank ℤ L) ⊕ ρ → Fin g → ℂ :=
    Sum.elim lam fun j => emb (Pi.single j (2 * Real.pi * Complex.I))
  have hle : Submodule.span ℝ (K : Set (Fin g → ℂ)) ≤ Submodule.span ℝ (Set.range f) := by
    refine Submodule.span_le.2 fun v hv => ?_
    have hv' : p v ∈ L := (h₁ v).2 ⟨0, by simpa using hv⟩
    let c := b.repr ⟨p v, hv'⟩
    have hc : p v = ∑ j, c j • (b j : Fin n → ℂ) := by
      have := congrArg Subtype.val (b.sum_repr ⟨p v, hv'⟩)
      rw [Submodule.coe_sum] at this
      exact this.symm
    have h0 : v - ∑ j, c j • lam j ∈ LinearMap.ker p := by
      rw [LinearMap.mem_ker, map_sub, map_sum, hc]
      simp only [map_zsmul, hpl, sub_self]
    rw [hker] at h0
    obtain ⟨s, hs⟩ := h0
    have hsK : emb s ∈ K := hs ▸ K.sub_mem hv (K.sum_mem fun j _ => K.zsmul_mem (hlam j) _)
    choose a ha using (h₂ s).1 hsK
    have hs' : s = ∑ j, a j • Pi.single j (2 * Real.pi * Complex.I : ℂ) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply, ha]
    have hv2 : v = ∑ j, c j • lam j + ∑ j, a j • emb (Pi.single j (2 * Real.pi * Complex.I : ℂ)) := by
      rw [eq_add_of_sub_eq' hs.symm, hs', map_sum]
      simp only [map_zsmul]
    rw [SetLike.mem_coe, hv2]
    exact add_mem (sum_mem fun j _ => zsmul_mem (Submodule.subset_span (Set.mem_range_self (f := f) (Sum.inl j))) _)
      (sum_mem fun j _ => zsmul_mem (Submodule.subset_span (Set.mem_range_self (f := f) (Sum.inr j))) _)
  have h3 := (Submodule.finrank_mono hle).trans (finrank_range_le_card (R := ℝ) f)
  rw [Fintype.card_sum, Fintype.card_fin, hb] at h3
  omega

section Torus

open GlobalTheory.PeriodSpan.TorusExp

theorem exists_torus_exp (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] :
    ∃ (r : ℕ) (e : (Fin r → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ splitTorus (Sp ℂ) Y)), (∀ s s', e (s + s') = e s * e s') ∧
      Function.Surjective e ∧ IsHolTo Set.univ (fun s => (show Sp ℂ ⟶ _ from (e s).left)) ∧
      ∀ s, e s = 1 ↔ ∀ j, ∃ a : ℤ, s j = a * (2 * Real.pi * Complex.I) := by
  let b := Module.finBasis ℤ Y
  let m : (Fin (Module.finrank ℤ Y) → ℂ) → Y →+ ℂ := fun s => (b.constr ℕ s).toAddMonoidHom
  have hm : ∀ s x, m s x = ∑ j, (b.repr x j : ℂ) * s j := fun s x => by
    change b.constr ℕ s x = _
    rw [b.constr_apply_fintype ℕ]
    simp
  have hmb : ∀ s j, m s (b j) = s j := fun s j => b.constr_basis ℕ s j
  refine ⟨_, fun s => expPt (m s), fun s s' => ?_, fun τ => ?_, ?_, fun s => ?_⟩
  · have : m (s + s') = m s + m s' := by
      ext x
      simp [hm, mul_add, Finset.sum_add_distrib]
    exact (congrArg expPt this).trans (expPt_add _ _)
  · obtain ⟨l, rfl⟩ := exists_eq_expPt τ
    refine ⟨fun j => ((2 * Real.pi * Complex.I : ℂ) • l) (b j), congrArg expPt ?_⟩
    exact AddMonoidHom.toIntLinearMap_injective (b.ext fun j => hmb _ j)
  · have hfst : ∀ s, (show Sp ℂ ⟶ _ from (expPt (m s)).left) ≫
        pullback.fst (splitTorusAff ZU Y).hom (toZ (Spec (.of ℂ))) = spMap (expRing (m s)) := fun s => by
      refine (pullback.lift_fst _ _ _).trans ?_
      rw [Spec.map_comp]
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) (toSpecΓ_SpecMap_ΓSpecIso_inv (CommRingCat.of ℂ))).trans (Category.id_comp _))
    have hsnd : ∀ s, (show Sp ℂ ⟶ _ from (expPt (m s)).left) ≫
        pullback.snd (splitTorusAff ZU Y).hom (toZ (Spec (.of ℂ))) = 𝟙 (Sp ℂ) :=
      fun s => Over.w (expPt (m s))
    have hd : ∀ x, Differentiable ℂ fun s => m s x := fun x => by
      simp only [hm]
      fun_prop
    have hol1 : IsHolTo Set.univ fun s => spMap (expRing (m s)) := by
      refine GlobalTheory.ThetaValueCont.isHolTo_spMap isOpen_univ _ fun a => ?_
      induction a using AddMonoidAlgebra.induction_linear with
      | zero => simp only [map_zero]; exact differentiableOn_const _
      | add a b ha hb => simp only [map_add]; exact ha.add hb
      | single x r =>
        exact (((hd x).cexp).const_mul (r.down : ℂ)).differentiableOn.congr fun s _ => expRing_single _ _ _
    refine GlobalTheory.HolHom.isHolTo_of_holAt isOpen_univ fun z _ => ?_
    refine GlobalTheory.HolHom.holAt_of_isPullback
      (IsPullback.of_hasPullback (splitTorusAff ZU Y).hom (toZ (Spec (.of ℂ)))) ?_ ?_
    · exact (funext hfst).symm ▸ GlobalTheory.HolHom.holAt_of_isHolTo hol1 trivial
    · exact (funext hsnd).symm ▸ GlobalTheory.HolHom.holAt_const _ _
  · constructor
    · intro h j
      have h' : expPt (m s) = expPt 0 := h.trans expPt_zero.symm
      have h1 := congrArg (fun τ => SplitTorus.val τ (b j)) h'
      simp only [val_expPt] at h1
      have h2 := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv.injective h1
      rw [hmb, AddMonoidHom.zero_apply, Complex.exp_zero] at h2
      exact Complex.exp_eq_one_iff.1 h2
    · intro h
      choose a ha using h
      refine Eq.trans (SplitTorus.hom_ext fun x => ?_) (expPt_zero (Λ := Y))
      rw [val_expPt, val_expPt, AddMonoidHom.zero_apply, Complex.exp_zero]
      congr 1
      refine Complex.exp_eq_one_iff.2 ⟨∑ j, b.repr x j * a j, ?_⟩
      rw [hm]
      simp [ha, Finset.sum_mul, _root_.mul_assoc]

end Torus

theorem cubWeil_of_weilIs (φ : Fib ℂ) {k : ℕ} {T : Over (Sp ℂ)} {x y : T ⟶ φ.G} (hx : x ^ k = 1) (hy : y ^ k = 1)
    {ζ : Γ(T.left, ⊤)ˣ} (h : Out.WeilIs φ.P.A φ.P.L k (x ≫ φ.q) (y ≫ φ.q) ζ) : GlobalTheory.UU.CubWeil φ.cub k x y ζ := by
  obtain ⟨ξ, hξ, -⟩ := GlobalTheory.UU.existsUnique_cubWeil φ.cub hx hy
  have hw : φ.q.left ≫ φ.P.A.hom = φ.G.hom ≫ 𝟙 _ := (Over.w φ.q).trans (Category.comp_id _).symm
  let σ : T ⟶ Over.mk (T.hom ≫ 𝟙 _) := Over.homMk (𝟙 T.left) (by simp)
  have h1 := (GlobalTheory.UU.cubWeil_of_isPullCubical _ _ (𝟙 _) φ.P.A φ.G (CubeMap.ofHom φ.q) hw
    (GlobalTheory.UU.toBase_mul_of_isMonHom φ.q hw) _ _ φ.cubB φ.cub φ.pull k T x y ξ hξ).comp σ
  have e : ∀ a : T ⟶ φ.G, σ ≫ Out.toBase hw a = a ≫ φ.q := fun a => Over.OverMorphism.ext (Category.id_comp _)
  have e' : Units.map σ.left.appTop.hom.toMonoidHom ξ = ξ := Units.ext (by
    change (Scheme.Hom.appTop (𝟙 T.left)).hom ξ.val = _
    simp)
  have h2 : GlobalTheory.UU.CubWeil φ.cubB k (x ≫ φ.q) (y ≫ φ.q) ξ := by
    rw [← e, ← e, ← e']
    exact h1
  have h3 := (GlobalTheory.UU.cubWeil_iff_weilIs (c := φ.cubB) GlobalTheory.globalFns_holds φ.P.isAb h2.1 h2.2.1 ζ).2 h
  exact h2.unique h3 ▸ hξ

theorem exists_ptEquiv {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] {G' : Over (Sp ℂ)} [GrpObj G']
    [IsCommMonObj G'] {z : Sp ℂ ⟶ X} (m : CubeMap G' G) (hp : IsGrpPullback G' G z m.F) {L : RigLB G} {L' : RigLB G'}
    {c : CubicalStr G L} {c' : CubicalStr G' L'} (hc : m.IsPullCubical c' c) :
    ∃ Φ : (𝟙_ (Over (Sp ℂ)) ⟶ G') ≃* (Over.mk z ⟶ G), (∀ a, (Φ a).left = a.left ≫ m.F) ∧
      ∀ (k : ℕ) a b (ζ : Γ(Sp ℂ, ⊤)ˣ), GlobalTheory.UU.CubWeil c' k a b ζ → GlobalTheory.UU.CubWeil c k (Φ a) (Φ b) ζ := by
  have hw := hp.1.w
  have hmul : ∀ (T : Over (Sp ℂ)) (x y : T ⟶ G'), Out.toBase hw (x * y) = Out.toBase hw x * Out.toBase hw y :=
    fun T x y => Over.OverMorphism.ext (hp.2 T x y _ _ rfl rfl).symm
  let U : Over (Sp ℂ) := 𝟙_ (Over (Sp ℂ))
  let ρ : Over.mk z ⟶ Over.mk (U.hom ≫ z) := Over.homMk (𝟙 _) rfl
  let Φ : (U ⟶ G') →* (Over.mk z ⟶ G) := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom ρ).comp (GlobalTheory.UU.toBaseHom hmul U)
  have hΦ : ∀ a : U ⟶ G', (Φ a).left = a.left ≫ m.F := fun a => Category.id_comp _
  have hb : Function.Bijective Φ := by
    refine ⟨fun a b h => Over.OverMorphism.ext (hp.1.hom_ext ?_ ?_), fun p => ?_⟩
    · rw [← hΦ, ← hΦ, h]
    · exact (Over.w a).trans (Over.w b).symm
    · refine ⟨Over.homMk (hp.1.lift p.left (𝟙 _) ((Over.w p).trans (Category.id_comp _).symm))
        (hp.1.lift_snd _ _ _), Over.OverMorphism.ext ((hΦ _).trans (hp.1.lift_fst _ _ _))⟩
  refine ⟨MulEquiv.ofBijective Φ hb, hΦ, fun k a b ζ h => ?_⟩
  have h2 := (GlobalTheory.UU.cubWeil_of_isPullCubical _ _ z G G' m hw hmul _ _ c c' hc k U _ _ _ h).comp ρ
  have e' : Units.map ρ.left.appTop.hom.toMonoidHom ζ = ζ := Units.ext (by
    change (Scheme.Hom.appTop (𝟙 (Sp ℂ))).hom ζ.val = _
    simp)
  rw [← e']
  exact h2

theorem exists_tangent_lift (φ : Fib ℂ) (v : epsR ℂ ⟶ φ.P.A) (hv : IsTangent v) :
    ∃ v' : epsR ℂ ⟶ φ.G, IsTangent v' ∧ v' ≫ φ.q = v := by
  have := TangentLift.smooth_q φ
  have h0 : η[φ.G].left ≫ φ.q.left = η[φ.P.A].left := congrArg (·.left) (IsMonHom.one_hom φ.q)
  obtain ⟨w, hw, hq⟩ := TangentLift.exists_lift_of_isNilpotent φ.q.left
    (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩)
    ⟨2, by
      rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
      intro a ha b hb
      have ha' : a.fst = 0 := ha
      have hb' : b.fst = 0 := hb
      rw [Ideal.mem_bot]
      ext <;> simp [ha', hb']⟩ v.left η[φ.G].left (h0.trans hv.symm)
    (η[φ.G].left (IsLocalRing.closedPoint ℂ)) (fun p => congrArg η[φ.G].left (Subsingleton.elim (α := PrimeSpectrum ℂ) _ _))
  exact ⟨Over.homMk w (by rw [← Over.w φ.q, reassoc_of% hq]; exact Over.w v), hw, Over.OverMorphism.ext hq⟩

theorem countable_ker {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} (t : SAB H X) (z : Sp ℂ ⟶ X) {g : ℕ} (ex : (Fin g → ℂ) → (Over.mk z ⟶ t.G)) (he : IsExpAt t z ex)
    (hol : IsHolTo Set.univ (fun w => (ex w).left)) : {w | ex w = 1}.Countable := by
  have h := isLatFam_ker E H X t 0 g Set.univ (fun _ => z) (fun _ => ex) isOpen_univ
    (GlobalTheory.HolHom.isHolTo_of_holAt (isOpen_univ.prod isOpen_univ) fun q _ =>
      (GlobalTheory.HolHom.holAt_of_isHolTo hol (Set.mem_univ q.2)).precomp differentiableAt_snd) fun _ _ => he
  have : DiscreteTopology {w | ex w = 1} := by
    refine isDiscrete_iff_discreteTopology.1 (isDiscrete_iff_nhdsNE.2 fun w hw => ?_)
    obtain ⟨ζ, h0, -, hev⟩ := h.2.2.2 0 trivial w hw
    have h1 := (Continuous.prodMk_right (0 : Fin 0 → ℂ)).continuousAt.eventually hev
    rw [Filter.inf_principal_eq_bot]
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with x hx hne hx'
    exact hne ((hx.1 hx').trans h0)
  exact Set.countable_coe_iff.1 (TopologicalSpace.separableSpace_iff_countable.1 inferInstance)

theorem exists_linear_to_abelian_part : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (z : Sp ℂ ⟶ X) (g : ℕ) (ex : (Fin g → ℂ) → (Over.mk z ⟶ t.G)), IsExpAt t z ex → IsHolTo Set.univ (fun w => (ex w).left) → ∀ (φ : Fib ℂ) (m : CubeMap φ.G t.G), FibAt t z φ m → ∀ (n : ℕ), φ.P.g = n → ∀ (u : HolUnif φ.P.A φ.P.L n) (Hm : Matrix (Fin n) (Fin n) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ → ∃ π : (Fin g → ℂ) →ₗ[ℂ] (Fin n → ℂ), (∀ (w : Fin g → ℂ) (v' : epsR ℂ ⟶ φ.G) (W : Fin n → ℂ), IsDerivAt0 (fun s => (ex s).left) w (v'.left ≫ m.F) → u.IsDiff W (v' ≫ φ.q) → W = π w) ∧ Submodule.span ℝ (π '' {w | ex w = 1}) = ⊤ ∧ Module.finrank ℝ (Submodule.span ℝ {w | ex w = 1}) + Module.finrank ℂ (LinearMap.ker π) ≤ 2 * g ∧ ∀ (k : ℕ) (v w : Fin g → ℂ) (ζ : ℂˣ), 0 < k → ex v = 1 → ex w = 1 → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm Hm (π v) (π w)).im : ℂ) / k) → GlobalTheory.UU.CubWeil t.cub k (ex ((k : ℂ)⁻¹ • v)) (ex ((k : ℂ)⁻¹ • w)) (unitOn ζ) := by
  intro E _ _ _ H X t z g ex hexp hol φ m hφ n _ u Hm χ hAH
  obtain ⟨hp, -, hc⟩ := hφ
  obtain ⟨Φ, hΦ, hΦw⟩ := exists_ptEquiv m hp hc
  have hcount := countable_ker t z ex hexp hol
  obtain ⟨hadd, -, hd2⟩ := hexp
  have h0 : ex 0 = 1 := GlobalTheory.HolHom.map_zero_eq_one hadd
  obtain ⟨-, -, -, -, ht1, ht2, -⟩ := AHWeil.tangent_and_weil_of_isAH thetaUnifAV_all φ.P n u Hm χ hAH
  let e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ φ.G) := fun w => Φ.symm (ex w)
  have heΦ : ∀ w, Φ (e w) = ex w := fun w => Φ.apply_symm_apply _
  have heF : ∀ w, (e w).left ≫ m.F = (ex w).left := fun w => by rw [← hΦ, heΦ]
  have heF' : (fun w => (show Sp ℂ ⟶ _ from (e w).left) ≫ m.F) = fun w => (ex w).left := funext heF
  have eadd : ∀ v w, e (v + w) = e v * e w := fun v w => by simp only [e, hadd, map_mul]
  have e0 : e 0 = 1 := GlobalTheory.HolHom.map_zero_eq_one eadd
  have e1 : ∀ w, e w = 1 ↔ ex w = 1 := fun w => Φ.symm.map_eq_one_iff
  have es : ∀ w, (show Sp ℂ ⟶ _ from (e w).left) ≫ φ.G.hom = 𝟙 _ := fun w => Over.w (e w)
  have holF : IsHolTo Set.univ (fun w => (show Sp ℂ ⟶ _ from (e w).left) ≫ m.F) := heF' ▸ hol
  have hole : IsHolTo Set.univ (fun w => (show Sp ℂ ⟶ _ from (e w).left)) :=
    FibreUnif.isHolTo_of_isPullback hp.1 es holF
  obtain ⟨π, hπ, -⟩ := existsUnique_linear_lift_of_isHolTo φ.P.A φ.P.isAb φ.P.L n g u ht1 ht2 (fun w => e w ≫ φ.q)
    (fun v w => by rw [eadd, MonObj.mul_comp]) (HolFibre.isHolTo_comp hole φ.q.left)
  have u0 : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem
  have one_left : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ φ.P.A).left = η[φ.P.A].left := by
    rw [Hom.one_def, toUnit_unit, Category.id_comp]
  have one_left' : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ φ.G).left = η[φ.G].left := by
    rw [Hom.one_def, toUnit_unit, Category.id_comp]
  have hder : ∀ (w : Fin g → ℂ) (v' : epsR ℂ ⟶ φ.G) (W : Fin n → ℂ),
      IsDerivAt0 (fun s => (ex s).left) w (v'.left ≫ m.F) → u.IsDiff W (v' ≫ φ.q) → W = π w := by
    intro w v' W hd hW
    have d1 : IsDerivAt0 (fun w => (show Sp ℂ ⟶ _ from (e w).left)) w v'.left :=
      FibreDeriv.isDerivAt0_of_isPullback hp.1 es holF (Over.w v') (heF' ▸ hd)
    have d2 := FibreDeriv.isDerivAt0_comp d1 φ.q.left
    have hq : (fun w => (show Sp ℂ ⟶ _ from (e w).left) ≫ φ.q.left) =
        fun w => (show Sp ℂ ⟶ _ from (u.ex (π w)).left) := funext fun w => by rw [hπ]; rfl
    rw [hq] at d2
    have d3 := (DetLine.FibreCmp.isDerivAt0_comp_linear (fun w => (show Sp ℂ ⟶ _ from (u.ex w).left))
      (fun U f => by simpa using u.hol U f) π w _).1 d2
    have htan : IsTangent (v' ≫ φ.q) := d3.1.trans (by rw [← one_left, ← u0])
    exact (ht1 _ htan).unique hW d3.2
  have hsurj : Function.Surjective π := by
    intro W
    obtain ⟨v, ⟨hv, hW⟩, -⟩ := ht2 W
    obtain ⟨v', hv', rfl⟩ := exists_tangent_lift φ v hv
    obtain ⟨w, hw, -⟩ := hd2 (v'.left ≫ m.F) ⟨by
      rw [Category.assoc, hp.1.w, ← Category.assoc, Over.w v']
      rfl, by
      rw [← Category.assoc, hv', ← one_left', ← h0, ← heF, e0]⟩
    exact ⟨w, (hder w v' W hw hW).symm⟩
  obtain ⟨r, τ, τadd, τsurj, τhol, τker⟩ := exists_torus_exp φ.X
  have := φ.i_hom
  obtain ⟨emb, hemb, -⟩ := GlobalTheory.HolHom.existsUnique_linear (e := fun s => Φ (τ s ≫ φ.i)) (e' := ex)
    (fun v w => by rw [τadd, MonObj.mul_comp, map_mul]) hadd
    (by
      have h := HolFibre.isHolTo_comp (HolFibre.isHolTo_comp τhol φ.i.left) m.F
      simp only [hΦ]
      exact h) hol
    (fun v hv => hd2 v.left ⟨Over.w v, by rw [hv, h0]⟩)
  have hemb' : ∀ s, e (emb s) = τ s ≫ φ.i := fun s => Φ.injective (by rw [heΦ, hemb])
  have esub : ∀ v w, e (v - w) = 1 ↔ e v = e w := fun v w => by
    have h := eadd (v - w) w
    rw [sub_add_cancel] at h
    rw [h]
    exact mul_eq_right.symm
  let K : AddSubgroup (Fin g → ℂ) :=
    { carrier := {w | ex w = 1}
      zero_mem' := h0
      add_mem' := fun {a b} (ha : ex a = 1) (hb : ex b = 1) => show ex (a + b) = 1 by rw [hadd, ha, hb, _root_.mul_one]
      neg_mem' := fun {a} (ha : ex a = 1) => show ex (-a) = 1 by
        have h := hadd (-a) a
        rw [neg_add_cancel, h0, ha, _root_.mul_one] at h
        exact h.symm }
  have hK : ∀ w, w ∈ K ↔ e w = 1 := fun w => (e1 w).symm
  have hiq : ∀ a : 𝟙_ (Over (Sp ℂ)) ⟶ splitTorus (Sp ℂ) φ.X, (a ≫ φ.i) ≫ φ.q = 1 := fun a => by
    rw [Category.assoc, φ.isKernel.w, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  have h₁ : ∀ w, π w ∈ u.Λ ↔ ∃ s, w - emb s ∈ K := fun w => by
    rw [← u.ker, hπ]
    constructor
    · intro h
      obtain ⟨s, hs⟩ := τsurj (φ.isKernel.lift (e w) (toUnit _) h)
      exact ⟨s, (hK _).2 ((esub _ _).2 (by rw [hemb', hs, IsPullback.lift_fst]))⟩
    · rintro ⟨s, hs⟩
      rw [(esub _ _).1 ((hK _).1 hs), hemb', hiq]
  have h₂ : ∀ s, emb s ∈ K ↔ ∀ j, ∃ a : ℤ, s j = a * (2 * Real.pi * Complex.I) := fun s => by
    rw [hK, hemb', ← τker]
    exact ⟨fun h => φ.isKernel.hom_ext (by rw [h, MonObj.one_comp]) (toUnit_unique _ _),
      fun h => by rw [h, MonObj.one_comp]⟩
  have := u.discrete
  obtain ⟨hspan, hrank⟩ := span_and_rank K hcount π hsurj u.Λ u.full emb h₁ h₂
  refine ⟨π, hder, hspan, hrank, fun k v w ζ hk hv hw hζ => ?_⟩
  have hΛ : ∀ v, ex v = 1 → π v ∈ u.Λ := fun v hv => (h₁ v).2 ⟨0, by rw [map_zero, sub_zero]; exact hv⟩
  have hpow : ∀ v, ex v = 1 → e ((k : ℂ)⁻¹ • v) ^ k = 1 := fun v hv => by
    have h := (AddMonoidHom.mk' (fun z => Additive.ofMul (e z)) eadd).map_nsmul k ((k : ℂ)⁻¹ • v)
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ (Nat.cast_ne_zero.2 hk.ne')] at h
    exact Eq.trans (Eq.symm h) ((e1 v).2 hv)
  have hW := AHWeilAny.weilIs_exp_riemannForm φ.P.A φ.P.isAb φ.P.L φ.P.isLB n u Hm χ hAH k (π v) (π w) ζ hk
    (hΛ v hv) (hΛ w hw) hζ
  rw [← map_smul, ← map_smul, hπ, hπ] at hW
  rw [← heΦ, ← heΦ]
  exact hΦw k _ _ _ (cubWeil_of_weilIs φ (hpow v hv) (hpow w hw) hW)

end GlobalTheory.FibExpAb

end
