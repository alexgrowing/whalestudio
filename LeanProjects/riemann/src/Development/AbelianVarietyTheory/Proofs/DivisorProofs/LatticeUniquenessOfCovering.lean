import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartOfMaximal

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison

open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover exists_sec_of_cover)
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.ChainPts.LatUniq

section General

variable {X : Scheme.{0}} [IsIntegral X] {F G : X.Modules} {U : X.Opens} {r r' : ℕ}

theorem resM_inj (hG : GlobalTheory.VB.IsVB G r') (hU : (U : Set X).Nonempty) {V : X.Opens} {s t : Γ(G, V)}
    (h : resM G (inf_le_left : V ⊓ U ≤ V) s = resM G inf_le_left t) : s = t := by
  choose W e _ hx hle he using fun x : V => hG.exists_affine (V := V) x.2
  refine sec_ext_of_cover W hle (fun x hxV => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxV⟩, hx _⟩) fun x => ?_
  refine ((he x).basis le_rfl).repr.injective (Finsupp.ext fun i => ?_)
  obtain ⟨y, hy⟩ := nonempty_preirreducible_inter (W x).isOpen U.isOpen ⟨_, hx x⟩ hU
  haveI : Nonempty (W x ⊓ U : X.Opens) := ⟨⟨y, hy⟩⟩
  refine map_injective_of_isIntegral X (homOfLE (inf_le_left : W x ⊓ U ≤ W x)) ?_
  have k := congrArg (resM G (inf_le_inf_right U (hle x))) h
  rw [resM_resM, resM_resM] at k
  have k₁ := (he x).repr_resM le_rfl (inf_le_left : W x ⊓ U ≤ W x) (resM G (hle x) s) i
  have k₂ := (he x).repr_resM le_rfl (inf_le_left : W x ⊓ U ≤ W x) (resM G (hle x) t) i
  rw [resM_resM] at k₁ k₂
  exact k₁.symm.trans ((congrArg (fun q => ((he x).basis _).repr q i) k).trans k₂)

theorem hom_ext (hG : GlobalTheory.VB.IsVB G r') (hU : (U : Set X).Nonempty) {s : Fin r → Γ(F, U)} (hs : GlobalTheory.VB.IsFrame s)
    {u v : F ⟶ G} (h : ∀ i, u.app U (s i) = v.app U (s i)) : u = v := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext σ
  refine resM_inj hG hU ?_
  change resM G _ (u.app V σ) = resM G _ (v.app V σ)
  rw [← app_resM, ← app_resM, ← (hs.basis (inf_le_right : V ⊓ U ≤ U)).sum_repr (resM F inf_le_left σ)]
  simp only [map_sum, Scheme.Modules.Hom.app_smul, GlobalTheory.VB.IsFrame.basis_apply, app_resM, h]

theorem exists_hom (hG : GlobalTheory.VB.IsVB G r') (hU : (U : Set X).Nonempty) {s : Fin r → Γ(F, U)} {s' : Fin r → Γ(G, U)}
    (hs : GlobalTheory.VB.IsFrame s) (hs' : GlobalTheory.VB.IsFrame s')
    (H : ∀ x : X, ∃ (V : X.Opens) (e : Fin r → Γ(F, V)) (t : Fin r → Γ(G, V)), x ∈ V ∧ GlobalTheory.VB.IsFrame e ∧
      ∀ j, resM G inf_le_left (t j) = hs.equiv hs' (inf_le_right : V ⊓ U ≤ U) (resM F inf_le_left (e j))) :
    ∃ u : F ⟶ G, ∀ i, u.app U (s i) = s' i := by
  have nat {V W : X.Opens} (h : W ≤ V) {σ : Γ(F, V)} {τ : Γ(G, V)}
      (k : resM G inf_le_left τ = hs.equiv hs' (inf_le_right : V ⊓ U ≤ U) (resM F inf_le_left σ)) :
      resM G inf_le_left (resM G h τ) = hs.equiv hs' (inf_le_right : W ⊓ U ≤ U) (resM F inf_le_left (resM F h σ)) := by
    have k' := congrArg (resM G (inf_le_inf_right U h)) k
    rw [← hs.equiv_resM, resM_resM, resM_resM] at k'
    rw [resM_resM, resM_resM]
    exact k'
  have ex (V : X.Opens) (σ : Γ(F, V)) : ∃ τ : Γ(G, V),
      resM G inf_le_left τ = hs.equiv hs' (inf_le_right : V ⊓ U ≤ U) (resM F inf_le_left σ) := by
    have loc (x : V) : ∃ (W : X.Opens) (h : W ≤ V) (τ : Γ(G, W)), x.1 ∈ W ∧
        resM G inf_le_left τ = hs.equiv hs' (inf_le_right : W ⊓ U ≤ U) (resM F inf_le_left (resM F h σ)) := by
      obtain ⟨W, e, t, hx, he, ht⟩ := H x
      refine ⟨V ⊓ W, inf_le_left, ∑ j, (he.basis inf_le_right).repr (resM F inf_le_left σ) j • resM G inf_le_right (t j),
        ⟨x.2, hx⟩, ?_⟩
      conv_rhs => rw [← (he.basis (inf_le_right : V ⊓ W ≤ W)).sum_repr (resM F inf_le_left σ)]
      simp only [map_sum, resM_smul, map_smul, GlobalTheory.VB.IsFrame.basis_apply, nat inf_le_right (ht _)]
    choose W hW τ hx hτ using loc
    have hc : V ≤ iSup W := fun x hxV => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxV⟩, hx _⟩
    obtain ⟨t, ht⟩ := exists_sec_of_cover W hW hc τ fun x y => resM_inj hG hU (by
      rw [nat inf_le_left (hτ x), nat inf_le_right (hτ y), resM_resM, resM_resM, resM_resM, resM_resM])
    refine ⟨t, sec_ext_of_cover (fun x => W x ⊓ U) (fun x => inf_le_inf_right U (hW x))
      (fun x hxV => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxV.1⟩, hx _, hxV.2⟩) fun x => ?_⟩
    have k := hτ x
    rw [← ht x, resM_resM, resM_resM] at k
    rw [← hs.equiv_resM, resM_resM, resM_resM]
    exact k
  choose u hu using ex
  refine ⟨GlobalTheory.LB.homOfLinear (fun V =>
    { toFun := u V
      map_add' := fun a b => resM_inj hG hU (by simp only [map_add, hu])
      map_smul' := fun a b => resM_inj hG hU (by simp only [resM_smul, map_smul, hu, RingHom.id_apply]) })
    fun h σ => resM_inj hG hU ((hu _ _).trans (nat h (hu _ σ)).symm), fun i => resM_inj hG hU ?_⟩
  exact (hu U (s i)).trans (hs.equiv_resM_frame hs' _ i)

omit [IsIntegral X] in

theorem coef_mul {V : X.Opens} {e : Fin r → Γ(F, V)} {s : Fin r → Γ(F, U)} (he : GlobalTheory.VB.IsFrame e)
    (hs : GlobalTheory.VB.IsFrame s) (j l : Fin r) :
    ∑ i, coef true he hs j i * coef false he hs l i = if j = l then 1 else 0 := by
  have k := (hs.basis (inf_le_right : V ⊓ U ≤ U)).sum_repr (resM F inf_le_left (e j))
  have k' := congrArg (fun q => (he.basis (inf_le_left : V ⊓ U ≤ V)).repr q l) k
  simp only [map_sum, map_smul, GlobalTheory.VB.IsFrame.basis_apply, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul] at k'
  refine k'.trans ?_
  rw [← he.basis_apply, Module.Basis.repr_self, Finsupp.single_apply]

omit [IsIntegral X] in

theorem equiv_eq_sum {V : X.Opens} {e : Fin r → Γ(F, V)} {e' : Fin r → Γ(G, V)} {s : Fin r → Γ(F, U)}
    {s' : Fin r → Γ(G, U)} (he : GlobalTheory.VB.IsFrame e) (he' : GlobalTheory.VB.IsFrame e') (hs : GlobalTheory.VB.IsFrame s)
    (hs' : GlobalTheory.VB.IsFrame s') (j : Fin r) :
    hs.equiv hs' (inf_le_right : V ⊓ U ≤ U) (resM F inf_le_left (e j)) =
      ∑ l, (∑ i, coef true he hs j i * coef false he' hs' l i) • resM G inf_le_left (e' l) := by
  rw [← (hs.basis (inf_le_right : V ⊓ U ≤ U)).sum_repr (resM F inf_le_left (e j))]
  simp only [map_sum, map_smul, GlobalTheory.VB.IsFrame.basis_apply, GlobalTheory.VB.IsFrame.equiv_resM_frame, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.smul_sum]
  congr 1
  rw [← (he'.basis (inf_le_left : V ⊓ U ≤ V)).sum_repr (resM G inf_le_right (s' i))]
  simp only [GlobalTheory.VB.IsFrame.basis_apply]
  rfl

omit [IsIntegral X] in

theorem exists_local {V : X.Opens} {e : Fin r → Γ(F, V)} {e' : Fin r → Γ(G, V)} {s : Fin r → Γ(F, U)}
    {s' : Fin r → Γ(G, U)} (he : GlobalTheory.VB.IsFrame e) (he' : GlobalTheory.VB.IsFrame e') (hs : GlobalTheory.VB.IsFrame s)
    (hs' : GlobalTheory.VB.IsFrame s') {x : X} (hx : x ∈ V)
    (H : ∀ j l : Fin r, ∃ (T : X.Opens) (hT : T ≤ V) (t : Γ(X, T)), x ∈ T ∧ resG X inf_le_left t =
      resG X (inf_le_inf_right U hT) (∑ i, coef true he hs j i * coef false he' hs' l i)) :
    ∃ (V : X.Opens) (e : Fin r → Γ(F, V)) (t : Fin r → Γ(G, V)), x ∈ V ∧ GlobalTheory.VB.IsFrame e ∧
      ∀ j, resM G inf_le_left (t j) = hs.equiv hs' (inf_le_right : V ⊓ U ≤ U) (resM F inf_le_left (e j)) := by
  choose T hT t hxT ht using fun q : Fin r × Fin r => H q.1 q.2
  obtain ⟨V', hxV, hle, hV⟩ : ∃ V' : X.Opens, x ∈ V' ∧ V' ≤ V ∧ ∀ q, V' ≤ T q :=
    ⟨V ⊓ Finset.univ.inf T, ⟨hx, by rw [TopologicalSpace.Opens.coe_finset_inf]; simpa using hxT⟩, inf_le_left,
      fun q => inf_le_right.trans (Finset.inf_le (Finset.mem_univ q))⟩
  refine ⟨V', _, fun j => ∑ l, resG X (hV (j, l)) (t (j, l)) • resM G hle (e' l), hxV, he.res hle, fun j => ?_⟩
  have k := congrArg (resM G (inf_le_inf_right U hle)) (equiv_eq_sum he he' hs hs' j)
  rw [← GlobalTheory.VB.IsFrame.equiv_resM, resM_resM] at k
  rw [resM_resM]
  refine Eq.trans ?_ k.symm
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [resM_smul, resM_smul, resM_resM, resM_resM]
  have k' := congrArg (resG X (inf_le_inf_right U (hV (j, l)))) (ht (j, l))
  rw [GlobalTheory.LB.resG_resG, GlobalTheory.LB.resG_resG] at k'
  rw [GlobalTheory.LB.resG_resG, k']

omit [IsIntegral X] in

theorem exists_frames (vF : GlobalTheory.VB.IsVB F r) (vG : GlobalTheory.VB.IsVB G r') (x : X) :
    ∃ (V : X.Opens) (e : Fin r → Γ(F, V)) (e' : Fin r' → Γ(G, V)), x ∈ V ∧ GlobalTheory.VB.IsFrame e ∧ GlobalTheory.VB.IsFrame e' := by
  obtain ⟨V₁, e₁, hx₁, he₁⟩ := vF x
  obtain ⟨V, e', -, hx, hle, he'⟩ := vG.exists_affine hx₁
  exact ⟨V, _, e', hx, he₁.res hle, he'⟩

end General

section Model

open GlobalTheory.FieldPtGlue GlobalTheory.ShFam.Pad.Pull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z : LocM.Mdl Y i₀}

theorem exists_ext (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) [IsDiscreteValuationRing (Z.i.c.V W)]
    {B : Vert.Model (Z.i.c.V W)} (hN : GlobalTheory.IsNormalScheme B.X) (h : B.X ⟶ Z.X) {a₀ : Fin Z.m}
    (ha : ((h ⁻¹ᵁ (Z.U a₀).1 : B.X.Opens) : Set B.X).Nonempty) {U : B.X.Opens} (f : Γ(B.X, U ⊓ h ⁻¹ᵁ (Z.U a₀).1))
    (hb : ∀ (y : Z.Pt) (w : Sp ↥(intO ↥y.C.S) ⟶ B.X), w ≫ h = y.z → ⊤ ≤ y.gen ⁻¹ᵁ (Z.U a₀).1 →
      ⊤ ≤ w ⁻¹ᵁ U → ‖valF (spMap (intO ↥y.C.S).subtype ≫ w) _ f‖ ≤ 1)
    {x : B.X} (hx : x ∈ U) (hpx : (p : B.X.residueField x) = 0) :
    ∃ (V : B.X.Opens) (l : V ≤ U) (t : Γ(B.X, V)), x ∈ V ∧
      resG B.X inf_le_left t = resG B.X (inf_le_inf_right _ l) f := by
  have : IsLocallyNoetherian B.X := inferInstance
  let R : Type := B.X.presheaf.stalk x
  obtain ⟨_, _⟩ : IsDomain R ∧ IsIntegrallyClosed R := (GlobalTheory.isNormalScheme_iff _).1 hN x
  let K := FractionRing R
  let ι : Sp R ⟶ B.X := B.X.fromSpecStalk x
  have hι (q : Sp R) : ι q ⤳ x := (B.X.range_fromSpecStalk (x := x)).le ⟨q, rfl⟩
  let w₀ : Sp K ⟶ B.X := spMap (algebraMap R K) ≫ ι
  have hη : w₀ (closedPoint K) ⤳ x := hι _
  have hm : ∀ y : B.X, y ⤳ w₀ (closedPoint K) → y = w₀ (closedPoint K) :=
    GenId.maximal_of_stalk (IsFractionRing.injective R K)
  have hgen : genericPoint B.X = w₀ (closedPoint K) := hm _ ((genericPoint_spec B.X).specializes (Set.mem_univ _))
  have ha₀ : w₀ (closedPoint K) ∈ h ⁻¹ᵁ (Z.U a₀).1 := by
    rw [← hgen]
    exact ((genericPoint_spec B.X).mem_open_set_iff (h ⁻¹ᵁ (Z.U a₀).1).isOpen).2 (by simpa using ha)
  have w₀a : ⊤ ≤ w₀ ⁻¹ᵁ (h ⁻¹ᵁ (Z.U a₀).1) := (le_preimage_iff _).2 ha₀
  have w₀U : ⊤ ≤ w₀ ⁻¹ᵁ U := (le_preimage_iff _).2 (hη.mem_open U.isOpen hx)
  obtain ⟨φ₀, -⟩ := exists_fromSpec (Z.U a₀).2 (w₀ ≫ h) fun q hq => w₀a hq
  have : CharZero K := (φ₀.comp (Z.alg a₀)).charZero_iff (RingHom.injective _) |>.1 inferInstance
  have hc : Cardinal.mk R ≤ Cardinal.continuum := by
    obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (X := B.X) hx
    let σ : Z.i.c.V W →+* Γ(B.X, V) := (Spec.preimage (hV.fromSpec ≫ B.str)).hom
    have e : spMap σ = hV.fromSpec ≫ B.str := Spec.map_preimage _
    have h2 : LocallyOfFiniteType (spMap σ) := by rw [e]; infer_instance
    have hσ : σ.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h2
    letI := B.X.presheaf.algebra_section_stalk (⟨x, hxV⟩ : V)
    have := hV.isLocalization_stalk ⟨x, hxV⟩
    exact (IsLocalization.cardinalMk_le (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl).trans
      (HTLine.Dvd.mk_le_of_finiteType σ hσ
        ((Cardinal.mk_subtype_le _).trans ((Cardinal.mk_subtype_le _).trans Cardinal.mk_complex.le)))
  obtain ⟨ρ, hρ⟩ := GenId.mem_range_of_norm_le (R := R) (K := K) hp
    ((residue_eq_zero_iff _).1 ((map_natCast _ p).trans hpx)) hc (κ := valF w₀ _ f) fun C ψ θ e => by
      have g : spMap (intO ↥C.S).subtype ≫ spMap ψ ≫ ι = spMap θ ≫ w₀ := by
        rw [← Category.assoc, ← Category.assoc, ModelRelProbe.spMap_comp, ModelRelProbe.spMap_comp, e]
      have g' : spMap (intO ↥C.S).subtype ≫ spMap ψ ≫ ι ≫ h = spMap θ ≫ w₀ ≫ h := by
        rw [← Category.assoc (spMap ψ), ← Category.assoc, g, Category.assoc]
      obtain ⟨Q, hQ⟩ := ModelPt.exists_ptC E H Dw Xo p W Y i₀ hp hW Z C (spMap ψ ≫ ι ≫ h) (by
        rintro _ ⟨q, rfl⟩
        rw [g', ← Z.cover]
        exact Set.mem_iUnion.2 ⟨a₀, w₀a (Set.mem_univ (spMap θ q))⟩)
      let y : Z.Pt := ⟨C, Q, spMap ψ ≫ ι ≫ h, hQ⟩
      have hy : y.gen = spMap θ ≫ w₀ ≫ h := g'
      have := hb y (spMap ψ ≫ ι) (Category.assoc _ _ _) (by rw [hy]; exact fun q _ => w₀a (Set.mem_univ (spMap θ q)))
        fun q _ => (hι (spMap ψ q)).mem_open U.isOpen hx
      rwa [g, GenId.valF_map θ (U := U ⊓ h ⁻¹ᵁ (Z.U a₀).1) fun q hq => ⟨w₀U hq, w₀a hq⟩] at this
  obtain ⟨V₁, hx₁, t₁, rfl⟩ := B.X.presheaf.germ_exist ρ
  obtain ⟨V, hV, hxV, hle⟩ := exists_isAffineOpen_mem_and_subset (X := B.X) (x := x) (U := V₁ ⊓ U) ⟨hx₁, hx⟩
  have l₁ : V ≤ V₁ := fun q hq => (hle hq).1
  have l₂ : V ≤ U := fun q hq => (hle hq).2
  have v : valF w₀ V (resG B.X l₁ t₁) = valF w₀ _ f := by
    have e : w₀ = spMap ((algebraMap R K).comp (B.X.presheaf.germ V x hxV).hom) ≫ hV.fromSpec := by
      rw [← ModelRelProbe.spMap_comp, Category.assoc]
      exact congrArg (spMap (algebraMap R K) ≫ ·) (hV.fromSpecStalk_eq_fromSpecStalk hxV).symm
    rw [← hρ, e, valF_fromSpec]
    exact congrArg (algebraMap R K) (B.X.presheaf.germ_res_apply (homOfLE l₁) x hxV t₁)
  refine ⟨V, l₂, resG B.X l₁ t₁, hxV, GenId.ext_maximal fun η hη' hm' => ?_⟩
  obtain rfl : η = w₀ (closedPoint K) :=
    (hm' _ ((genericPoint_spec B.X).specializes (Set.mem_univ _))).symm.trans hgen
  have h' := (le_preimage_iff (x := w₀) _).2 hη'
  refine ⟨K, inferInstance, w₀, rfl, ?_⟩
  exact (valF_restrict _ h' _).trans (v.trans (valF_restrict _ h' _).symm)

theorem exists_comb {X₀ : Scheme.{0}} (t : SAB H X₀) {S : Type} [CommRing S] {x : Sp S ⟶ X₀} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hv : ∀ j, IsTanAtG t x (v j)) (c : Fin m → S) :
    ∃ w, IsCombAtG t x v c w :=
  ⟨_, fun i => Over.homMk (spMap (epsMul (c i)) ≫ v i) (by
    change (spMap (epsMul (c i)) ≫ v i) ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x
    rw [Category.assoc, (hv i).1, ← Category.assoc, ModelRelProbe.spMap_comp, epsMul_comp_alg]), fun _ => rfl, rfl⟩

theorem exists_ev {k : Type} [Field k] {X : Scheme.{0}} {w : Sp k ⟶ X} {U : X.Opens} (h : ⊤ ≤ w ⁻¹ᵁ U) :
    ∃ ev : Γ(X, U) →+* k, ∀ f, valF w U f = ev f :=
  ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.comp (w.appLE U ⊤ h).hom, fun _ => dif_pos h⟩

theorem norm_le {X : Scheme.{0}} {h : X ⟶ Z.X} {r : ℕ} {x : Fin r → Letter Dw} {d b : Bool} {F G : X.Modules}
    {s : ∀ a : Fin Z.m, Fin r → Γ(F, h ⁻¹ᵁ (Z.U a).1)} {s' : ∀ a : Fin Z.m, Fin r → Γ(G, h ⁻¹ᵁ (Z.U a).1)}
    (hF : IsLat Z h x d b F s) (hG : IsLat Z h x d b G s') (a : Fin Z.m) {V : X.Opens} {e : Fin r → Γ(F, V)}
    {e' : Fin r → Γ(G, V)} (he : GlobalTheory.VB.IsFrame e) (he' : GlobalTheory.VB.IsFrame e') (j l : Fin r) (y : Z.Pt)
    (w : Sp ↥(intO ↥y.C.S) ⟶ X) (hw : w ≫ h = y.z) (hy : ⊤ ≤ y.gen ⁻¹ᵁ (Z.U a).1) (hV : ⊤ ≤ w ⁻¹ᵁ V) :
    ‖valF (spMap (intO ↥y.C.S).subtype ≫ w) _
      (∑ i, coef true he (hF.frame a) j i * coef false he' (hG.frame a) l i)‖ ≤ 1 := by
  obtain ⟨φ, hφ⟩ := exists_fromSpec (Z.U a).2 y.gen hy
  have hg : y.gen = (spMap (intO ↥y.C.S).subtype ≫ w) ≫ h := by rw [Category.assoc, hw]; rfl
  obtain ⟨ev, hev⟩ := exists_ev (w := spMap (intO ↥y.C.S).subtype ≫ w) (U := V ⊓ h ⁻¹ᵁ (Z.U a).1)
    fun q hq => ⟨hV (Set.mem_univ (spMap (intO ↥y.C.S).subtype q)), by
      have := hy hq
      rw [hg] at this
      exact this⟩
  have key (cf : Fin r → ↥y.C.S) : (∀ l, ‖∑ i, cf i * ev (coef d he (hF.frame a) l i)‖ ≤ 1) ↔
      ∀ l, ‖∑ i, cf i * ev (coef d he' (hG.frame a) l i)‖ ≤ 1 := by
    obtain ⟨v, hv⟩ := exists_comb (Y Z.i).t (fun i => ((chart_frame Z hφ).1 (x i).1 (x i).2).1) cf
    have k := (hF.norm y w hw a φ hφ V e he hV cf v hv).symm.trans (hG.norm y w hw a φ hφ V e' he' hV cf v hv)
    simpa only [hev] using k
  rw [hev, map_sum]
  simp only [map_mul]
  cases d with
  | false =>
    refine (key fun i => ev (coef true he (hF.frame a) j i)).1 (fun m => ?_) l
    simp only [← map_mul, ← map_sum, coef_mul]
    split_ifs <;> simp
  | true =>
    simp only [mul_comm (ev (coef true _ _ _ _))]
    refine (key fun i => ev (coef false he' (hG.frame a) l i)).2 (fun m => ?_) j
    simp only [← map_mul, ← map_sum, mul_comm (coef false _ _ _ _), coef_mul]
    split_ifs <;> simp

theorem exists_hom_isLat (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) [IsDiscreteValuationRing (Z.i.c.V W)]
    {B : Vert.Model (Z.i.c.V W)} (hN : GlobalTheory.IsNormalScheme B.X) {h : B.X ⟶ Z.X} {a : Fin Z.m}
    (ha : ((h ⁻¹ᵁ (Z.U a).1 : B.X.Opens) : Set B.X).Nonempty) {r : ℕ} {x : Fin r → Letter Dw} {d b : Bool}
    {F G : B.X.Modules} (vF : GlobalTheory.VB.IsVB F r) (vG : GlobalTheory.VB.IsVB G r)
    {s : ∀ a : Fin Z.m, Fin r → Γ(F, h ⁻¹ᵁ (Z.U a).1)} {s' : ∀ a : Fin Z.m, Fin r → Γ(G, h ⁻¹ᵁ (Z.U a).1)}
    (hF : IsLat Z h x d b F s) (hG : IsLat Z h x d b G s') : ∃ u : F ⟶ G, ∀ i, u.app _ (s a i) = s' a i := by
  refine exists_hom vG ha (hF.frame a) (hG.frame a) fun z => ?_
  obtain ⟨z₀, hz, hz₀⟩ := GlobalTheory.TestPts.exists_special_V hp hW B z
  obtain ⟨V, e, e', hx, he, he'⟩ := exists_frames vF vG z₀
  obtain ⟨V', e₂, t, k₁, k₂⟩ := exists_local he he' (hF.frame a) (hG.frame a) hx fun j l =>
    exists_ext hp hW hN h ha (U := V) (∑ i, coef true he (hF.frame a) j i * coef false he' (hG.frame a) l i)
      (fun y w k₁ k₂ k₃ => norm_le hF hG a he he' j l y w k₁ k₂ k₃) hx hz₀
  exact ⟨V', e₂, t, hz.mem_open V'.isOpen k₁, k₂⟩

theorem exists_iso (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) [IsDiscreteValuationRing (Z.i.c.V W)]
    {B : Vert.Model (Z.i.c.V W)} (hN : GlobalTheory.IsNormalScheme B.X) {h : B.X ⟶ Z.X} {a : Fin Z.m}
    (ha : ((h ⁻¹ᵁ (Z.U a).1 : B.X.Opens) : Set B.X).Nonempty) {r : ℕ} {x : Fin r → Letter Dw} {d b : Bool}
    {Λ : Type} [CommRing Λ] {F G : AM B Λ} (vF : GlobalTheory.VB.IsVB F.V r) (vG : GlobalTheory.VB.IsVB G.V r)
    {s : ∀ a : Fin Z.m, Fin r → Γ(F.V, h ⁻¹ᵁ (Z.U a).1)} {s' : ∀ a : Fin Z.m, Fin r → Γ(G.V, h ⁻¹ᵁ (Z.U a).1)}
    (hF : IsLat Z h x d b F.V s) (hG : IsLat Z h x d b G.V s') (χ : Fin r → Λ → Γ(B.X, h ⁻¹ᵁ (Z.U a).1))
    (aF : ∀ i c, (F.ρ c : F.V ⟶ F.V).app _ (s a i) = χ i c • s a i)
    (aG : ∀ i c, (G.ρ c : G.V ⟶ G.V).app _ (s' a i) = χ i c • s' a i) :
    ∃ e : F ≅ G, ∀ i, e.hom.hom.app _ (s a i) = s' a i := by
  obtain ⟨u, hu⟩ := exists_hom_isLat hp hW hN ha vF vG hF hG
  obtain ⟨v, hv⟩ := exists_hom_isLat hp hW hN ha vG vF hG hF
  refine ⟨Action.mkIso ⟨u, v, hom_ext vF ha (hF.frame a) fun i => ?_, hom_ext vG ha (hG.frame a) fun i => ?_⟩
    fun c => hom_ext vG ha (hF.frame a) fun i => ?_, hu⟩
  · change v.app _ (u.app _ (s a i)) = s a i
    rw [hu, hv]
  · change u.app _ (v.app _ (s' a i)) = s' a i
    rw [hv, hu]
  · change u.app _ ((F.ρ c : F.V ⟶ F.V).app _ (s a i)) = (G.ρ c : G.V ⟶ G.V).app _ (u.app _ (s a i))
    rw [aF, hu, aG, Scheme.Modules.Hom.app_smul, hu]

theorem exists_iso_pres (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) [IsDiscreteValuationRing (Z.i.c.V W)]
    {B : Vert.Model (Z.i.c.V W)} (hN : GlobalTheory.IsNormalScheme B.X) {h : B.X ⟶ Z.X}
    (hopn : ∀ η : B.X, (∀ y : B.X, y ⤳ η → y = η) → h η ∈ Z.opn) {r : ℕ} {x : Fin r → Letter Dw} {d : Bool}
    {P P' : EPres B (𝓞 E)} (hP : IsEqLatPres Z h x d P) (hP' : IsEqLatPres Z h x d P') :
    ∃ (e : P.E ≅ P'.E) (e' : P.E' ≅ P'.E'), P.ψ ≫ e.hom = e'.hom ≫ P'.ψ := by
  obtain ⟨a, ha₀⟩ := GlobalTheory.TestPts.exists_chart_of_maximal h hopn (η := genericPoint B.X) fun y hy =>
    (hy.antisymm ((genericPoint_spec B.X).specializes (Set.mem_univ y))).eq
  have ha : ((h ⁻¹ᵁ (Z.U a).1 : B.X.Opens) : Set B.X).Nonempty := ⟨_, ha₀⟩
  obtain ⟨hr, s, h₁, h₂, h₃⟩ := hP
  obtain ⟨hr', s', h₁', h₂', h₃'⟩ := hP'
  have act {Q : EPres B (𝓞 E)} {U : B.X.Opens} {σ : Γ(Q.E'.V, U)} {c : 𝓞 E} {g : Γ(B.X, U)}
      (k : (Q.E'.ρ c : Q.E'.V ⟶ Q.E'.V).app _ σ = g • σ) :
      (Q.E.ρ c : Q.E.V ⟶ Q.E.V).app _ (Q.ψ.hom.app _ σ) = g • Q.ψ.hom.app _ σ := by
    have k' : (Q.E'.ρ c : Q.E'.V ⟶ Q.E'.V) ≫ Q.ψ.hom = Q.ψ.hom ≫ (Q.E.ρ c : Q.E.V ⟶ Q.E.V) := Q.ψ.comm c
    rw [← Scheme.Modules.Hom.app_smul, ← k]
    exact (congrArg (fun q => Scheme.Modules.Hom.app q U σ) k').symm
  obtain ⟨e', he'⟩ := exists_iso hp hW hN ha (hr ▸ P.vb') (hr' ▸ P'.vb') h₁ h₁' _ (h₃ a) (h₃' a)
  obtain ⟨e, he⟩ := exists_iso hp hW hN ha (hr ▸ P.vb) (hr' ▸ P'.vb) h₂ h₂' _ (fun i c => act (h₃ a i c))
    fun i c => act (h₃' a i c)
  refine ⟨e, e', Action.Hom.ext (hom_ext P'.vb ha (h₁.frame a) fun i => ?_)⟩
  change e.hom.hom.app _ (P.ψ.hom.app _ (s a i)) = P'.ψ.hom.app _ (e'.hom.hom.app _ (s a i))
  rw [he, he']

end Model

theorem latUniqueSt : LatUniqueSt := by
  intro D O hO p _ W hW jc hj z
  haveI := isDiscreteValuationRing_V z.Z.i.c (Fact.out : p.Prime) hW
  intro c B f hB _ r x d P P' hP hP'
  exact exists_iso_pres Fact.out hW hB (GlobalTheory.TestPts.mem_opn_comp Fact.out hW f) hP hP'

theorem latUniqueSt_of_classicalTheorems : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.ChainPts.LatUniqueSt := fun _ => latUniqueSt

end GlobalTheory.ChainPts.LatUniq
