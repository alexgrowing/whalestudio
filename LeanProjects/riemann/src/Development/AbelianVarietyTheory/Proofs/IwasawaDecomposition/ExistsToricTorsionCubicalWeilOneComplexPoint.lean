import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsToricTorsionCubWeilOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Laws3
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyFamilyUnifIffUnifAt
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FibTors

open GlobalTheory.Models GlobalTheory.UU

theorem exists_relDim_fibre (X : Scheme.{0}) (G : Over X) [GrpObj G] (hG : IsSemiAbelian G) (y : Sp ℂ ⟶ X) :
    ∃ n, SmoothOfRelativeDimension n ((Over.pullback y).obj G).hom := by
  have hG' : IsSemiAbelian ((Over.pullback y).obj G) := IsSemiAbelian.pullback y G hG
  have := hG'.smooth
  have := hG'.geomConnected
  have : ConnectedSpace ((Over.pullback y).obj G).left :=
    GeometricallyConnected.connectedSpace_of_subsingleton ((Over.pullback y).obj G).hom
  exact exists_dim_of_preconnected _ (((1 : 𝟙_ (Over (Sp ℂ)) ⟶ (Over.pullback y).obj G).left) (default : PrimeSpectrum ℂ))

theorem lieBasis_card (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (y : Sp ℂ ⟶ X) (g n : ℕ)
    (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (hadd : ∀ z w, e (z + w) = e z * e w)
    (h1 : ∀ w, ∃! v : epsPt y ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left)
    (h2 : ∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)
    (v : Fin n → (epsR ℂ ⟶ (Over.pullback y).obj G)) (hv : IsLieBasis v) : n = g := by
  classical
  let G' := (Over.pullback y).obj G
  have h0 : e 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  let ρ : epsPt y ⟶ Over.mk ((epsR ℂ).hom ≫ y) := Over.homMk (𝟙 _) rfl
  let T : (epsR ℂ ⟶ G') →* (epsPt y ⟶ G) :=
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom ρ).comp (toBaseHom (toBase_mul_pullback G y) (epsR ℂ))
  have hT : ∀ a, (T a).left = a.left ≫ pullback.fst G.hom y := fun a => Category.id_comp _
  let U : Over (Sp ℂ) := 𝟙_ (Over (Sp ℂ))
  let ρ0 : Over.mk y ⟶ Over.mk (U.hom ≫ y) := Over.homMk (𝟙 _) rfl
  let φ : (U ⟶ G') →* (Over.mk y ⟶ G) :=
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom ρ0).comp (toBaseHom (toBase_mul_pullback G y) U)
  have hη : η[G'].left ≫ pullback.fst G.hom y = (1 : Over.mk y ⟶ G).left := by
    have h' : (φ 1).left = (1 : U ⟶ G').left ≫ pullback.fst G.hom y := Category.id_comp _
    rw [map_one] at h'
    rw [h']
    congr 2
  have hTb : Function.Bijective T := by
    refine ⟨fun a b h => Over.OverMorphism.ext (pullback.hom_ext ?_ ?_), fun p => ?_⟩
    · rw [← hT, ← hT, h]
    · exact (Over.w a).trans (Over.w b).symm
    · refine ⟨Over.homMk (pullback.lift p.left (epsR ℂ).hom (Over.w p)) (pullback.lift_snd _ _ _),
        Over.OverMorphism.ext ((hT _).trans (pullback.lift_fst _ _ _))⟩
  have htan : ∀ a : epsR ℂ ⟶ G', IsTangent a ↔
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (T a).left = (e 0).left := by
    intro a
    rw [h0, hT, ← hη]
    refine ⟨fun h => by rw [← Category.assoc, h], fun h => pullback.hom_ext ?_ ?_⟩
    · rw [Category.assoc]; exact h
    · have e1 : a.left ≫ pullback.snd G.hom y = (epsR ℂ).hom := Over.w a
      have e2 : η[G'].left ≫ pullback.snd G.hom y = 𝟙 _ := Over.w η[G']
      rw [Category.assoc, e1, e2]
      show spMap _ ≫ spMap _ = _
      rw [GlobalTheory.TanMod.spMap_comp']
      have : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp (algebraMap ℂ (DualNumber ℂ)) = RingHom.id ℂ :=
        RingHom.ext fun _ => rfl
      rw [this]
      exact Spec.map_id _
  let Te := MulEquiv.ofBijective T hTb
  have hTe : ∀ a, Te a = T a := fun _ => rfl
  choose D hD _ using h1
  have hDmul : ∀ w w', D (w + w') = D w * D w' := fun w w' =>
    Over.OverMorphism.ext (GlobalTheory.VerticalDeriv.isDerivAt0_unique (hD (w + w'))
      (GlobalTheory.UnifCompare.isDerivAt0_mul (congrArg (·.left) h0) (hD w) (hD w')))
  have hDtan : ∀ w, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (D w).left = (e 0).left := fun w => (hD w).1
  let Dl : (Fin g → ℂ) → (epsR ℂ ⟶ G') := fun w => Te.symm (D w)
  have hTDl : ∀ w, T (Dl w) = D w := fun w => Te.apply_symm_apply (D w)
  have hDl_tan : ∀ w, IsTangent (Dl w) := fun w => (htan _).2 (by rw [hTDl]; exact hDtan w)
  have hDl_add : ∀ w w', Dl (w + w') = Dl w * Dl w' := fun w w' => by
    apply Te.injective
    rw [map_mul, hTe, hTe, hTe, hTDl, hTDl, hTDl, hDmul]
  have hDl_zero : Dl 0 = 1 := by
    have := hDl_add 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hDl_smul : ∀ (c : ℂ) w, (Dl (c • w)).left = spMap (epsScaleR c) ≫ (Dl w).left := by
    intro c w
    have hov : (spMap (epsScaleR c) ≫ (Dl w).left) ≫ G'.hom = (epsR ℂ).hom := by
      rw [Category.assoc, Over.w (Dl w)]
      show spMap _ ≫ spMap _ = spMap _
      rw [GlobalTheory.TanMod.spMap_comp']
      have hc : (epsScaleR c).comp (algebraMap ℂ (DualNumber ℂ)) = algebraMap ℂ (DualNumber ℂ) :=
        RingHom.ext fun a => by ext <;> simp [epsScaleR]
      rw [hc]
    let a : epsR ℂ ⟶ G' := Over.homMk (spMap (epsScaleR c) ≫ (Dl w).left) hov
    have ha : T a = D (c • w) := by
      refine Over.OverMorphism.ext (GlobalTheory.VerticalDeriv.isDerivAt0_unique ?_ (hD (c • w)))
      rw [hT]
      have := GlobalTheory.UnifCompare.isDerivAt0_smul (hD w) c
      rw [← hTDl w, hT] at this
      show IsDerivAt0 _ _ ((spMap (epsScaleR c) ≫ (Dl w).left) ≫ pullback.fst G.hom y)
      rw [Category.assoc]
      exact this
    have : a = Dl (c • w) := by
      apply Te.injective
      rw [hTe, hTe, ha, hTDl]
    rw [← this]
    rfl
  have hDl_inj : ∀ w w', Dl w = Dl w' → w = w' := by
    intro w w' h
    have h' : D w = D w' := by rw [← hTDl, ← hTDl, h]
    exact (h2 (D w) (hDtan w)).unique (hD w) (h' ▸ hD w')
  have hDl_onto : ∀ a, IsTangent a → ∃ w, Dl w = a := by
    intro a ha
    obtain ⟨w, hw, -⟩ := h2 (T a) ((htan a).1 ha)
    refine ⟨w, Te.injective ?_⟩
    rw [Te.apply_symm_apply, hTe]
    exact Over.OverMorphism.ext (GlobalTheory.VerticalDeriv.isDerivAt0_unique (hD w) hw)
  have hsum : ∀ (k : ℕ) (f : Fin k → Fin g → ℂ), Dl (∑ i, f i) = (List.ofFn fun i => Dl (f i)).prod := by
    intro k
    induction k with
    | zero => intro f; simp [hDl_zero]
    | succ k ih =>
      intro f
      rw [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons, hDl_add, ih]
  choose ws hws using fun i => hDl_onto (v i) (hv.1 i)
  have hcomb : ∀ c : Fin n → ℂ, IsLieComb c v (Dl (∑ i, c i • ws i)) := by
    intro c
    refine ⟨fun i => Dl (c i • ws i), fun i => ?_, hsum n _⟩
    rw [hDl_smul, hws]
  have hdet : ∀ (c : Fin n → ℂ) (a a' : epsR ℂ ⟶ G'), IsLieComb c v a → IsLieComb c v a' → a = a' := by
    rintro c a a' ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
    have : u = u' := funext fun i => Over.OverMorphism.ext ((hu i).trans (hu' i).symm)
    rw [this]
  have hli : LinearIndependent ℂ ws := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have e1 := hcomb c
    rw [hc] at e1
    have e2 := hcomb 0
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at e2
    have := (hv.2 (Dl 0) (hDl_tan 0)).unique e1 e2
    exact fun i => congrFun this i
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range ws) := by
    intro w _
    obtain ⟨c, hc, -⟩ := hv.2 (Dl w) (hDl_tan w)
    have := hDl_inj _ _ (hdet c _ _ hc (hcomb c))
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hb := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
  simpa using hb.symm

end GlobalTheory.FibTors

open GlobalTheory.FibTors GlobalTheory.Models GlobalTheory.UU in

theorem GlobalTheory.exists_toric_torsion_cubWeil_one_of_exp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (y : Sp ℂ ⟶ X) (g N : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)), 0 < N → IsExpAt t y e → Function.Surjective e → IsHolTo Set.univ (fun w => (e w).left) → ∃ T : Set (Over.mk y ⟶ t.G), (∀ τ ∈ T, τ ^ N = 1) ∧ (∀ τ ∈ T, ∀ x : Over.mk y ⟶ t.G, x ^ N = 1 → GlobalTheory.UU.CubWeil t.cub N τ x 1) ∧ Nat.card {p : Over.mk y ⟶ t.G // p ^ N = 1} * Nat.card T = N ^ (2 * g) := by
  intro E _ _ _ H X t y g N e hN hexp _ _
  obtain ⟨hadd, hd1, hd2⟩ := hexp
  have h0 : e 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have h1 : ∀ w, ∃! v : epsPt y ⟶ t.G, IsDerivAt0 (fun z => (e z).left) w v.left := by
    intro w
    obtain ⟨v, ⟨hv1, hv2⟩, hu⟩ := hd1 w
    refine ⟨Over.homMk v hv1.1, hv2, fun v' hv' => Over.OverMorphism.ext (hu v'.left ⟨⟨Over.w v', ?_⟩, hv'⟩)⟩
    refine hv'.1.trans ?_
    show (e 0).left = _
    rw [h0]
  have h2 : ∀ v : epsPt y ⟶ t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left := by
    intro v hv
    exact hd2 v.left ⟨Over.w v, by rw [hv, h0]⟩
  obtain ⟨n, hn⟩ := exists_relDim_fibre X t.G t.semi y
  obtain ⟨v, hv⟩ := GlobalTheory.KeyPow.exists_isLieBasis _ hn
  have hng := lieBasis_card X t.G y g n e hadd h1 h2 v hv
  subst hng
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  let G : Over X := t.G
  let x := y
  let k := ℂ
  have h3 := GlobalTheory.laws3
  let G' : Over (Sp k) := (Over.pullback x).obj G
  have hp : IsGrpPullback G' G x (pullback.fst G.hom x) := isGrpPullback_pullback G x
  have hG' : IsSemiAbelian G' := IsSemiAbelian.pullback x G t.semi
  have := hG'.comm
  have := hG'.smooth
  have := hG'.geomConnected
  have dG' : SmoothOfRelativeDimension n G'.hom := hn
  obtain ⟨E⟩ := t.semi.fibres k x
  let := E.addCommGroup
  let := E.grpB
  have := E.free
  have := E.finite
  have := E.i_hom
  obtain ⟨hL, hr, ⟨c', hc'⟩, -⟩ := h3.cubePull _ _ G G' (cubeMapOf hp) t.PP t.cub
  obtain ⟨σ⟩ := GlobalTheory.BiextTriv.main k E.X G' _ c' E.i E.i_hom
  have hw : pullback.fst G.hom x ≫ G.hom = G'.hom ≫ x := pullback.condition
  let U : Over (Sp k) := 𝟙_ (Over (Sp k))
  let ρ : Over.mk x ⟶ Over.mk (U.hom ≫ x) := Over.homMk (𝟙 _) rfl
  let φ : (U ⟶ G') →* (Over.mk x ⟶ G) := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom ρ).comp (toBaseHom (toBase_mul_pullback G x) U)
  have hφ : ∀ a : U ⟶ G', (φ a).left = a.left ≫ pullback.fst G.hom x := fun a => Category.id_comp _
  have hb : Function.Bijective φ := by
    refine ⟨fun a b h => Over.OverMorphism.ext (pullback.hom_ext ?_ ?_), fun p => ?_⟩
    · rw [← hφ, ← hφ, h]
    · exact (Over.w a).trans (Over.w b).symm
    · refine ⟨Over.homMk (pullback.lift p.left (𝟙 _) ((Over.w p).trans (Category.id_comp _).symm))
        (pullback.lift_snd _ _ _), Over.OverMorphism.ext ((hφ _).trans (pullback.lift_fst _ _ _))⟩
  let e' := MulEquiv.ofBijective φ hb
  have he : ∀ a : U ⟶ G', e' a ^ N = 1 ↔ a ^ N = 1 := fun a => by rw [← map_pow, e'.map_eq_one_iff]
  have hcount := GlobalTheory.card_torsion_mul_card_toric_torsion k G' E n N hG' dG' hN'
  refine ⟨e' '' {y | y ^ N = 1 ∧ ∃ t, y = t ≫ E.i}, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ⟨ha, -⟩, rfl⟩
    exact (he a).2 ha
  · rintro _ ⟨_, ⟨ha, s0, rfl⟩, rfl⟩ y hy
    obtain ⟨b, rfl⟩ := e'.surjective y
    have ht : s0 ^ N = 1 := E.isKernel.hom_ext
      (by rw [MonObj.pow_comp, ha, MonObj.one_comp]) (toUnit_unique _ _)
    have h1 := σ.cubWeil ht ((he b).1 hy)
    have h2 := (GlobalTheory.UU.cubWeil_of_isPullCubical _ _ x G G' (cubeMapOf hp) hw (toBase_mul_pullback G x) t.PP _ t.cub c' hc' N U _ _ _ h1).comp ρ
    rw [map_one] at h2
    exact h2
  · rw [← hcount]
    congr 1
    · exact (Nat.card_congr (e'.toEquiv.subtypeEquiv fun a => (he a).symm)).symm
    · exact Nat.card_image_of_injective e'.injective _
