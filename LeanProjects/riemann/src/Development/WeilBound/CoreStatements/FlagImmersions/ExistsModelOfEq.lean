import Development.WeilBound.CoreStatements.FlagImmersions.Transport
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLie
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PairSumFrameAtPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeLimit
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointPolarisedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixChangeFrameStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointLatticeDataStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreLatticeLinearEquivStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace RootFieldNumerics

namespace FV

section Stalk

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G]

theorem exists_model_of_eq {R : Type} [CommRing R] {z z' : Sp R ⟶ X} (h : z = z') {E : Type} [AddCommGroup E]
    [Module R E] (M : LieModel G z E) : ∃ M' : LieModel G z' E, ∀ e, (M'.pt e).left = (M.pt e).left := by
  subst h
  exact ⟨M, fun _ => rfl⟩

theorem stalk_model [IsCommMonObj G] [Smooth G.hom] {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li)
    (hξ : IsCptGen ξ) {L : Type} [Field L] (z : Sp L ⟶ X) (h : genPt ξ ⤳ centre z) {V : Type} [AddCommGroup V]
    [Module L V] (Mz : LieModel G z V) :
    ∃ (T : Type) (_ : AddCommGroup T) (_ : Module (X.presheaf.stalk (centre z)) T)
      (M0 : LieModel (R := X.presheaf.stalk (centre z)) G (X.fromSpecStalk (centre z)) T) (i : T →+ Li) (β : T →+ V),
      (∀ t, M.Extends ⟨centre z, h⟩ (i t) (M0.pt t)) ∧
      (∀ t, Mz.pt (β t) = LieTangent.epsBase _ (LieTangent.spec_centre z) ≫ M0.pt t) ∧
      (∀ (a : X.presheaf.stalk (centre z)) t, i (a • t) = genMap ξ ⟨centre z, h⟩ a • i t) ∧
      (∀ (a : X.presheaf.stalk (centre z)) t, β (a • t) = (Scheme.stalkClosedPointTo z).hom a • β t) ∧
      (∀ e ∈ M.lat ⟨centre z, h⟩, ∃ t, i t = e) ∧
      (∀ ψ : T →+ L, (∀ (a : X.presheaf.stalk (centre z)) t, ψ (a • t) = (Scheme.stalkClosedPointTo z).hom a * ψ t) →
        ∃ F : V →ₗ[L] L, ∀ t, F (β t) = ψ t) ∧
      ∀ P : Submodule L V, (∀ t, β t ∈ P) → P = ⊤ := by
  obtain ⟨T, iT, mT, ⟨M0⟩⟩ := lieModel_exists X G (X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z))
  let q : Cpt ξ := ⟨centre z, h⟩
  have exi : ∀ t, ∃ e, M.pt e = LieTangent.epsBase (genMap ξ q) (LieTangent.spec_genMap ξ q) ≫ M0.pt t := fun t =>
    M.onto _ (LieTangent.isTanAt_base _ _ (M0.tan t))
  choose fi hfi using exi
  have exb : ∀ t, ∃ x, Mz.pt x = LieTangent.epsBase _ (LieTangent.spec_centre z) ≫ M0.pt t := fun t =>
    Mz.onto _ (LieTangent.isTanAt_base _ _ (M0.tan t))
  choose fb hfb using exb
  let i : T →+ Li := AddMonoidHom.mk' fi fun a b => M.inj (by rw [M.add, hfi, hfi, hfi, M0.add, comp_mul])
  let β : T →+ V := AddMonoidHom.mk' fb fun a b => Mz.inj (by rw [Mz.add, hfb, hfb, hfb, M0.add, comp_mul])
  have hi : ∀ t, M.pt (i t) = LieTangent.epsBase (genMap ξ q) (LieTangent.spec_genMap ξ q) ≫ M0.pt t := hfi
  have hβ : ∀ t, Mz.pt (β t) = LieTangent.epsBase _ (LieTangent.spec_centre z) ≫ M0.pt t := hfb
  have hext : ∀ t, M.Extends q (i t) (M0.pt t) := fun t => (M.extends_iff _ _ _).2 ⟨M0.tan t, hi t⟩
  have hsi : ∀ (a : X.presheaf.stalk (centre z)) t, i (a • t) = genMap ξ q a • i t := fun a t => M.inj (by
    rw [hi, LieModel.pt_smul, LieModel.pt_smul, hi, ← Category.assoc, LieTangent.base_scale, Category.assoc])
  have hsβ : ∀ (a : X.presheaf.stalk (centre z)) t, β (a • t) = (Scheme.stalkClosedPointTo z).hom a • β t :=
    fun a t => Mz.inj (by
      rw [hβ, LieModel.pt_smul, LieModel.pt_smul, hβ, ← Category.assoc, LieTangent.base_scale, Category.assoc]
      rfl)
  have honto : ∀ e ∈ M.lat q, ∃ t, i t = e := by
    intro e he
    obtain ⟨w, hw⟩ := (M.mem_lat_iff q e).1 he
    obtain ⟨t, rfl⟩ := M0.onto w hw.1
    refine ⟨t, M.inj ?_⟩
    rw [hi, ((M.extends_iff _ _ _).1 hw).2]
  letI alg : Algebra (X.presheaf.stalk (centre z)) L := (Scheme.stalkClosedPointTo z).hom.toAlgebra
  letI mV : Module (X.presheaf.stalk (centre z)) V := Module.compHom V (Scheme.stalkClosedPointTo z).hom
  have hmV : ∀ (a : X.presheaf.stalk (centre z)) (x : V), a • x = (Scheme.stalkClosedPointTo z).hom a • x :=
    fun _ _ => rfl
  haveI tower : IsScalarTower (X.presheaf.stalk (centre z)) L V :=
    ⟨fun a b x => by rw [Algebra.smul_def, hmV, mul_smul]; rfl⟩
  obtain ⟨M', hM'⟩ := exists_model_of_eq
    (show z = Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (centre z)) L)) ≫ X.fromSpecStalk (centre z)
      from (LieTangent.spec_centre z).symm) Mz
  let j : T →ₗ[X.presheaf.stalk (centre z)] V :=
    { toFun := β
      map_add' := map_add β
      map_smul' := fun a t => hsβ a t }
  have hbc : IsBaseChange L j := (PositivityTheory.HtPt.Htat.lie_proj X G (X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z)) T M0).2.2
    L V M' j fun t => by
      rw [hM']
      exact congrArg (fun w => w.left) (hβ t)
  refine ⟨T, iT, mT, M0, i, β, hext, hβ, hsi, hsβ, honto, fun ψ hψ => ?_, fun P hP => ?_⟩
  · let ψl : T →ₗ[X.presheaf.stalk (centre z)] L :=
      { toFun := ψ
        map_add' := map_add ψ
        map_smul' := fun a t => by
          rw [hψ, RingHom.id_apply, Algebra.smul_def]
          rfl }
    exact ⟨hbc.lift ψl, fun t => hbc.lift_eq ψl t⟩
  · refine eq_top_iff.2 fun x _ => ?_
    exact hbc.inductionOn x (· ∈ P) P.zero_mem hP (fun c n hn => P.smul_mem c hn) (fun _ _ => P.add_mem)

theorem exists_functional [IsCommMonObj G] [Smooth G.hom] {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li)
    (hξ : IsCptGen ξ) {L : Type} [Field L] (z : Sp L ⟶ X) (h : genPt ξ ⤳ centre z) {V : Type} [AddCommGroup V]
    [Module L V] (Mz : LieModel G z V) (f : Module.Dual Ω Li)
    (hf : ∀ e ∈ M.lat ⟨centre z, h⟩, f e ∈ regAt ξ ⟨centre z, h⟩) :
    ∃ g : V →ₗ[L] L, ∀ (e : Li) (x : V) (u : L), M.ValAt z e (Mz.pt x) → ValAt ξ z (f e) u → g x = u := by
  obtain ⟨T, _, _, M0, i, β, hext, hβ, hsi, -, -, hlift, -⟩ := stalk_model M hξ z h Mz
  have hgi : Function.Injective (genMap ξ ⟨centre z, h⟩) := hξ.inj ⟨centre z, h⟩
  have hs : ∀ t, ∃ s, genMap ξ ⟨centre z, h⟩ s = f (i t) := fun t => hf _ ((M.mem_lat_iff _ _).2 ⟨_, hext t⟩)
  choose σ hσ using hs
  obtain ⟨F, hF⟩ := hlift (AddMonoidHom.mk' (fun t => (Scheme.stalkClosedPointTo z).hom (σ t)) fun t t' => by
      have : σ (t + t') = σ t + σ t' := hgi (by simp [hσ])
      rw [this, map_add]) fun a t => by
    have : σ (a • t) = a * σ t := hgi (by rw [hσ, map_mul, hσ, hsi, map_smul, smul_eq_mul])
    show (Scheme.stalkClosedPointTo z).hom (σ (a • t)) = _ * (Scheme.stalkClosedPointTo z).hom (σ t)
    rw [this, map_mul]
  refine ⟨F, fun e x u hx hu => ?_⟩
  obtain ⟨h', v, hv, hw⟩ := hx
  obtain ⟨t, rfl⟩ := M0.onto v hv.1
  have e1 : i t = e := M.inj (Over.OverMorphism.ext ((hext t).2.trans hv.2.symm))
  have e2 : β t = x := Mz.inj (by
    rw [hβ]
    exact Over.OverMorphism.ext hw.symm)
  obtain ⟨_, s, hs, rfl⟩ := hu
  rw [← e2, hF]
  have : σ t = s := hgi (by rw [hσ, e1, hs])
  show (Scheme.stalkClosedPointTo z).hom (σ t) = _
  rw [this]

end Stalk

open GlobalTheory.CompanionTheory.Ar.HodgeMetric.GramEx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K]
  {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem exists_gram (𝔐 : HodgeCpt Y S y) {z : Sp ℂ ⟶ 𝔐.X} (hz : 𝔐.Interior z) (s : CMType H ⊕ CMType H) {N : ℕ}
    {b : Fin N → 𝔐.Li} (hb : (𝔐.V s).IsFrameAt b ⟨centre z, 𝔐.all _⟩) :
    (∀ k, b k ∈ 𝔐.Vgen s) ∧ ∃ Γ : Matrix (Fin N) (Fin N) ℂ, 𝔐.M.GramAt 𝔐.t.PP.L z b Γ ∧ Γ.PosDef := by
  have hgen : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := NumberField.RingOfIntegers.coe_injective
  have hξ : IsCptGen 𝔐.ξ := 𝔐.tie.gen
  obtain ⟨-, -, hc0, -, -, -, hind, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c _ _ Y S Ω K J y 𝔐 hβ
  have := hc0
  have hpol := GlobalTheory.T.interior_point_polarised E H D l Xo c Y S Ω K J y 𝔐 z hz
  obtain ⟨hV, -, hlat⟩ := GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c _ _ Y S Ω K J y 𝔐 hβ ⟨centre z, hgen⟩
    fun r hr => not_inFibre_centre hgen hr
  have hdR : ∀ k, b k ∈ 𝔐.dR s ⟨centre z, hgen⟩ := fun k => by
    have h1 : b k ∈ 𝔐.V s ⟨centre z, hgen⟩ := by
      rw [hb.2]
      exact Submodule.subset_span ⟨k, rfl⟩
    rwa [hV s] at h1
  refine ⟨fun k => (hdR k).2, ?_⟩
  let bb : Fin N → ↥(𝔐.Vgen s ⊔ 𝔐.Vgen s) := fun k => ⟨b k, Submodule.mem_sup_left (hdR k).2⟩
  have hspan : (Submodule.span (regAt 𝔐.ξ ⟨centre z, hgen⟩) (Set.range bb)).map
      ((𝔐.Vgen s ⊔ 𝔐.Vgen s).subtype.restrictScalars (regAt 𝔐.ξ ⟨centre z, hgen⟩)) =
      Submodule.span (regAt 𝔐.ξ ⟨centre z, hgen⟩) (Set.range b) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hfr : (Lat.comap (fun p => 𝔐.V s p ⊔ 𝔐.V s p) (𝔐.Vgen s ⊔ 𝔐.Vgen s).subtype).IsFrameAt bb
      ⟨centre z, hgen⟩ := by
    refine ⟨LinearIndependent.of_comp (𝔐.Vgen s ⊔ 𝔐.Vgen s).subtype hb.1, ?_⟩
    ext x
    constructor
    · intro hx
      have h1 : (x : 𝔐.Li) ∈ 𝔐.V s ⟨centre z, hgen⟩ ⊔ 𝔐.V s ⟨centre z, hgen⟩ := hx
      rw [sup_idem, hb.2, ← hspan] at h1
      obtain ⟨x', hx', e⟩ := h1
      have e' : x' = x := Subtype.ext e
      exact e' ▸ hx'
    · intro hx
      show (x : 𝔐.Li) ∈ 𝔐.V s ⟨centre z, hgen⟩ ⊔ 𝔐.V s ⟨centre z, hgen⟩
      rw [sup_idem, hb.2, ← hspan]
      exact ⟨x, hx, rfl⟩
  have hsm : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  obtain ⟨Vz, _, _, ⟨MR⟩⟩ := lieModel_exists 𝔐.X 𝔐.t.G ℂ z
  obtain ⟨f, hHI, hh, hp⟩ := GlobalTheory.T.hodge_hermitian_form_exists E H 𝔐.X 𝔐.t z Vz MR hpol
  obtain ⟨π, hπ, hreg⟩ := exists_dual_sum 𝔐 hind ⟨centre z, hgen⟩ hV hlat s s bb hfr
  have hval : ∀ k, ∃ x : Vz, 𝔐.M.ValAt z (b k) (MR.pt x) := fun k => by
    obtain ⟨w, hw⟩ := (𝔐.M.exists_valAt_iff z _).2 ⟨hgen, (hdR k).1⟩
    obtain ⟨x, rfl⟩ := MR.onto w hw.isTanAt
    exact ⟨x, hw⟩
  choose x hx using hval
  have hg : ∀ j, ∃ g : Vz →ₗ[ℂ] ℂ, ∀ k, g (x k) = if j = k then 1 else 0 := fun j => by
    obtain ⟨g, hg⟩ := exists_functional 𝔐.M hξ z hgen MR (π j) (hreg j)
    refine ⟨g, fun k => hg _ _ _ (hx k) ?_⟩
    have e := hπ j k
    change π j (b k) = _ at e
    rw [e]
    split_ifs
    · exact CxVal.one hgen
    · exact ⟨hgen, 0, map_zero _, map_zero _⟩
  choose g hg using hg
  exact ⟨Matrix.of fun p q => f (x p) (x q), ⟨fun k => MR.pt (x k), hx, fun p q => (hHI _ _ _).2 rfl⟩,
    posDef_of_dual f hh hp x g hg⟩

theorem linInd_of_posDef {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) {m : ℕ}
    (x : Fin m → Fin g → ℂ) (h : (R.gram x).PosDef) : LinearIndependent ℂ x := by
  refine Fintype.linearIndependent_iff.2 fun w hw => ?_
  have h0 : R.gram x *ᵥ w = 0 := by
    ext a
    have : (R.gram x *ᵥ w) a = (∑ i, w i • x i) ⬝ᵥ R.Hm *ᵥ star (x a) := by
      rw [sum_dotProduct]
      simp only [Matrix.mulVec, RiemLat.gram, RiemLat.ip, smul_dotProduct, smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [this, hw, zero_dotProduct, Pi.zero_apply]
  have := Matrix.eq_zero_of_mulVec_eq_zero h.det_pos.ne' h0
  exact fun i => congrFun this i

theorem finrank_eig_eq {g g' : ℕ} (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (B' : 𝓞 E →+* Module.End ℂ (Fin g' → ℂ))
    (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g' → ℂ)) (h : ∀ a p, φ (B a p) = B' a (φ p)) (s : 𝓞 E →+* ℂ) :
    Module.finrank ℂ (eigSp B s) = Module.finrank ℂ (eigSp B' s) := by
  have e : (eigSp B s).map φ.toLinearMap = eigSp B' s := by
    ext p
    obtain ⟨p, rfl⟩ := φ.surjective p
    have : φ p ∈ (eigSp B s).map φ.toLinearMap ↔ p ∈ eigSp B s :=
      ⟨fun ⟨q, hq, e⟩ => φ.injective e ▸ hq, fun hp => ⟨p, hp, rfl⟩⟩
    rw [this]
    simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    refine forall_congr' fun a => ?_
    rw [← h, ← φ.injective.eq_iff]
    simp
  rw [← e, LinearEquiv.finrank_map_eq]

end FV

theorem frameVals : FrameVals := by
  intro hG E _ _ _ H D l Xo c Y Ω _ K _ J _ y 𝔐 z s b h1 hz hb
  obtain ⟨hbs, Γ₀, hΓ₀, hp₀⟩ := FV.exists_gram 𝔐 hz s hb
  refine ⟨fun i => hΓ₀.elim fun v hv => ⟨_, hv.1 i⟩, ?_⟩
  intro g Λ _ _ R σ x v hσ hv hf
  have hgram : 𝔐.M.GramAt 𝔐.t.PP.L z b ((Real.pi : ℂ) • R.gram x) :=
    ⟨v, hv, fun p q => MuPsh.hodgeInnerProduct_of_fibreLatticeVector hf (fun a => (hv a).isTanAt) p q⟩
  obtain ⟨-, -, hc0, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c _ _ Y ∅ Ω K J y 𝔐 NumberField.RingOfIntegers.coe_injective
  have := hc0
  have e := GlobalTheory.T.gram_matrix_change_frame E H D l Xo c Y ∅ Ω K J y 𝔐 z _ b _ _ (GlobalTheory.T.interior_point_polarised E H D l Xo c Y ∅ Ω K J y 𝔐 z hz) hgram hΓ₀
  have hpos : (R.gram x).PosDef := by
    have h2 : R.gram x = ((Real.pi⁻¹ : ℝ) : ℂ) • Γ₀ := by
      rw [← e, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ Real.pi_ne_zero, Complex.ofReal_one, one_smul]
    rw [h2]
    exact hp₀.smul (Complex.zero_lt_real.2 (inv_pos.2 Real.pi_pos))
  have hli := FV.linInd_of_posDef R x hpos
  have hmem : ∀ i, x i ∈ eigSp R.B (σ s) := fun i => by
    refine (Submodule.mem_iInf _).2 fun a => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    obtain ⟨A, _, φ, u, χ, hpb, hAH, hact, -, -, h3⟩ := hf
    obtain ⟨v₁, e₁, d₁⟩ := h3 i
    obtain ⟨h1, w, hw, hr⟩ := hσ s a
    haveI := 𝔐.t.act.hom a
    have hsc := PhMuFree.val_eig 𝔐 𝔐.tie.gen h1 s a w hw (hbs i) (hv i)
    exact SheetPot.eig_of_isDiff hpb u (𝔐.t.act.act a) (R.B a) (fun p => hact a p) (hv i).isTanAt
      (c := σ s a) (by rw [← hr]; exact hsc) e₁ d₁
  obtain ⟨g', Λ', _, _, R', x', hf', -, hrk⟩ := GlobalTheory.T.interior_point_lattice_data hG.2.2.2.2.1 E H D l Xo c Y ∅ Ω K J y 𝔐 z h1 hz hG _ v
    fun i => (hv i).isTanAt
  obtain ⟨φ, -, -, hφ, -⟩ := GlobalTheory.T.fibre_lattice_linear_equiv E H 𝔐.X 𝔐.t z g g' Λ Λ' R R' _ x x' v hf hf'
  refine ⟨hli, ?_, hgram, hpos⟩
  refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 (Set.range_subset_iff.2 hmem)) ?_
  rw [finrank_span_eq_card hli, Fintype.card_fin, FV.finrank_eig_eq R.B R'.B φ hφ, hrk σ hσ s]

end RootFieldNumerics
