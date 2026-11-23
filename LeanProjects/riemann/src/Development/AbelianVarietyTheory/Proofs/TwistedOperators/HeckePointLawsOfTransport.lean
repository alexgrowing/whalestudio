import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHkIsogEtaleUnique
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckePointLaw

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori GlobalTheory.HeckeFrCompare GlobalTheory.ThetaTrace GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem finite_heckeKer {P : Ideal (𝓞 E)} {p : ℕ} (hp : 0 < p) (hP : (p : 𝓞 E) ∈ P) (i : ℕ) {Ω : Type} [Field Ω]
    [IsAlgClosed Ω] (x : Sp Ω ⟶ Xo.X) :
    Finite {C : Subgroup (Over.mk x ⟶ Xo.univ.t.G) // Xo.univ.t.HeckeKer (Over.mk x) Dw P p i C} := by
  have h₀ := (HeckeKerModel.heckeKer_zero Xo.univ Ω x _ (Spec.map_preimage (x ≫ Xo.s)).symm P (p ^ 2)
    (pow_pos hp 2)).2.2.2.2.1
  have hf : (Xo.univ.t.tors (Over.mk x) (Ideal.span {((p ^ 2 : ℕ) : 𝓞 E)})).Finite :=
    Nat.finite_of_card_ne_zero (h₀.trans_ne (pow_ne_zero _ (pow_pos hp 2).ne'))
  have := hf.finite_subsets.to_subtype
  refine Finite.of_injective (β := {b | b ⊆ Xo.univ.t.tors (Over.mk x) (Ideal.span {((p ^ 2 : ℕ) : 𝓞 E)})})
    (fun C => ⟨C.1, fun z hz a ha => C.2.2.2.1 hz a ?_⟩)
    fun C C' e => Subtype.ext (SetLike.coe_injective (congrArg Subtype.val e))
  refine (Ideal.span_singleton_le_iff_mem _).2 ?_ ha
  rw [Nat.cast_pow, pow_two]
  refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_
  have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hP
  rwa [map_natCast] at this

section Lie

variable {Ω : Type} [Field Ω]

abbrev epsBase (Ω : Type) [Field Ω] : Sp (DualNumber Ω) ⟶ Sp Ω := spMap (algebraMap Ω (DualNumber Ω))

abbrev epsZero (Ω : Type) [Field Ω] : Sp Ω ⟶ Sp (DualNumber Ω) := spMap (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom

theorem spMap_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem epsZero_base : epsZero Ω ≫ epsBase Ω = 𝟙 _ := by
  rw [spMap_spMap]
  exact (congrArg spMap (RingHom.ext fun _ => rfl)).trans (Spec.map_id _)

theorem eps_base (a : Ω) : spMap (epsMul a) ≫ epsBase Ω = epsBase Ω := by
  rw [spMap_spMap]
  refine congrArg spMap (RingHom.ext fun r => ?_)
  ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem epsZero_eps (a : Ω) : epsZero Ω ≫ spMap (epsMul a) = epsZero Ω := by
  rw [spMap_spMap]
  refine congrArg spMap (RingHom.ext fun r => ?_)
  simp [epsMul]

theorem eps_comm (a b : Ω) : spMap (epsMul a) ≫ spMap (epsMul b) = spMap (epsMul b) ≫ spMap (epsMul a) := by
  rw [spMap_spMap, spMap_spMap]
  refine congrArg spMap (RingHom.ext fun r => ?_)
  ext <;> simp [epsMul, mul_left_comm]

abbrev zeroAt (x : Sp Ω ⟶ Xo.X) : (Over.mk x : Over Xo.X) ⟶ tEps x := sec' x (epsZero Ω) epsZero_base

abbrev scaleAt (x : Sp Ω ⟶ Xo.X) (a : Ω) : tEps x ⟶ tEps x := res x (spMap (epsMul a)) (eps_base a)

theorem zeroAt_scaleAt (x : Sp Ω ⟶ Xo.X) (a : Ω) : zeroAt x ≫ scaleAt x a = zeroAt x :=
  Over.OverMorphism.ext (epsZero_eps a)

theorem scaleAt_comm (x : Sp Ω ⟶ Xo.X) (a b : Ω) : scaleAt x a ≫ scaleAt x b = scaleAt x b ≫ scaleAt x a :=
  Over.OverMorphism.ext (eps_comm a b)

theorem isTanAt_iff {x : Sp Ω ⟶ Xo.X} (a : tEps x ⟶ Xo.univ.t.G) : IsTanAt x a.left ↔ zeroAt x ≫ a = 1 :=
  ⟨fun h => Over.OverMorphism.ext h.2, fun h => ⟨Over.w a, congrArg (·.left) h⟩⟩

theorem isEigAt_iff {c : Coeff l} [Algebra c.F Ω] {x : Sp Ω ⟶ Xo.X} (τ : E →+* ℂ) (a : tEps x ⟶ Xo.univ.t.G) :
    IsEigAt c τ a.left ↔ ∀ r : 𝓞 E, a ≫ Xo.univ.t.act.act r = scaleAt x (algebraMap c.F Ω (embK c τ r)) ≫ a :=
  forall_congr' fun _ => ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg (·.left) h⟩

theorem isCombAt_iff {x : Sp Ω ⟶ Xo.X} {m : ℕ} (a : Fin m → (tEps x ⟶ Xo.univ.t.G)) (cf : Fin m → Ω)
    (b : tEps x ⟶ Xo.univ.t.G) :
    IsCombAt x (fun i => (a i).left) cf b.left ↔ (List.ofFn fun i => scaleAt x (cf i) ≫ a i).prod = b := by
  constructor
  · rintro ⟨u, hu, h⟩
    obtain rfl : u = fun i => scaleAt x (cf i) ≫ a i := funext fun i => Over.OverMorphism.ext (hu i)
    exact Over.OverMorphism.ext h
  · intro h
    exact ⟨_, fun _ => rfl, congrArg (·.left) h⟩

variable {x x' : Sp Ω ⟶ Xo.X} {Ψ : Gx x ⟶ Gx x'}

def tanMap (h : IsLinHom Ψ) : (tEps x ⟶ Xo.univ.t.G) →* (tEps x' ⟶ Xo.univ.t.G) :=
  MonoidHom.mk' (fun a => Over.homMk (push Ψ (epsBase Ω) a) (push_hom h.1 _ a)) fun a b =>
    Over.OverMorphism.ext (h.2.1 _ _ a b _ _ rfl rfl).symm

theorem tanMap_left (h : IsLinHom Ψ) (a : tEps x ⟶ Xo.univ.t.G) : (tanMap h a).left = push Ψ (epsBase Ω) a := rfl

theorem tanMap_scale (h : IsLinHom Ψ) (s : Ω) (a : tEps x ⟶ Xo.univ.t.G) :
    tanMap h (scaleAt x s ≫ a) = scaleAt x' s ≫ tanMap h a :=
  Over.OverMorphism.ext (push_res Ψ _ _ a)

theorem tanMap_act (h : IsLinHom Ψ) (r : 𝓞 E) (a : tEps x ⟶ Xo.univ.t.G) :
    tanMap h (a ≫ Xo.univ.t.act.act r) = tanMap h a ≫ Xo.univ.t.act.act r := by
  refine Over.OverMorphism.ext ?_
  have e : toFib x (epsBase Ω) (a ≫ Xo.univ.t.act.act r) =
      toFib x (epsBase Ω) a ≫ (Over.mk x ◁ Xo.univ.t.act.act r).left := by
    rw [toFib, toFib, ← Over.comp_left, lift_whiskerLeft]
  rw [Over.comp_left, tanMap_left, tanMap_left, push, push, e, Category.assoc, reassoc_of% (h.2.2 r),
    ← Over.comp_left, whiskerLeft_snd, Over.comp_left]
  simp only [Category.assoc]

theorem sends_one (h : IsLinHom Ψ) : Sends Ψ 1 1 := by
  obtain ⟨f, hf, -⟩ := exists_pointHom h
  simpa using hf 1

theorem tanMap_zero (h : IsLinHom Ψ) {a : tEps x ⟶ Xo.univ.t.G} (ha : zeroAt x ≫ a = 1) :
    zeroAt x' ≫ tanMap h a = 1 :=
  Over.OverMorphism.ext ((sends_sec'_iff h.1 (epsZero Ω) epsZero_base a 1).1 (by rw [ha]; exact sends_one h))

theorem existsUnique_tanMap (h : IsLinHom Ψ) [Etale Ψ] {w : tEps x' ⟶ Xo.univ.t.G} (hw : zeroAt x' ≫ w = 1) :
    ∃! a : tEps x ⟶ Xo.univ.t.G, zeroAt x ≫ a = 1 ∧ tanMap h a = w := by
  have e₀ : ∀ (y : Sp Ω ⟶ Xo.X) (a : tEps y ⟶ Xo.univ.t.G), zeroAt y ≫ a = 1 ↔
      epsZero Ω ≫ toFib y (epsBase Ω) a = (lift (𝟙 (Over.mk y)) (1 : Over.mk y ⟶ Xo.univ.t.G)).left := fun y a => by
    rw [← lift_sec' y _ epsZero_base]
    refine ⟨fun e => by rw [← e], fun e => Over.OverMorphism.ext ?_⟩
    rw [← lift_l_snd (𝟙 (Over.mk y)) (_ ≫ a), e, lift_l_snd]
  have e₁ : ∀ a : tEps x ⟶ Xo.univ.t.G, tanMap h a = w ↔ toFib x (epsBase Ω) a ≫ Ψ = toFib x' (epsBase Ω) w :=
    fun a => by
      refine ⟨fun e => gx_ext ?_ ?_, fun e => Over.OverMorphism.ext ?_⟩
      · rw [Category.assoc, h.1, toFib_fst, toFib_fst]
      · rw [toFib_snd, ← e, tanMap_left, push, Category.assoc]
      · rw [tanMap_left, push, reassoc_of% e, toFib_snd]
  obtain ⟨v, ⟨h₁, h₂⟩, hu⟩ := LieEtale.existsUnique_dual_lift Ψ (toFib x' (epsBase Ω) w)
    (lift (𝟙 (Over.mk x)) (1 : Over.mk x ⟶ Xo.univ.t.G)).left ((sends_one h).trans ((e₀ x' w).1 hw).symm)
  have hv : v ≫ (fst (Over.mk x) Xo.univ.t.G).left = epsBase Ω := by rw [← h.1, reassoc_of% h₂, toFib_fst]
  let a : tEps x ⟶ Xo.univ.t.G := Over.homMk (v ≫ (snd (Over.mk x) Xo.univ.t.G).left) (by
    rw [Category.assoc, snd_hom, reassoc_of% hv]; rfl)
  have ha : toFib x (epsBase Ω) a = v := gx_ext (by rw [toFib_fst, hv]) (by rw [toFib_snd]; rfl)
  refine ⟨a, ⟨(e₀ x a).2 (by rw [ha, h₁]), (e₁ a).2 (by rw [ha, h₂])⟩, fun b hb => Over.OverMorphism.ext ?_⟩
  rw [← toFib_snd x _ b, hu _ ⟨(e₀ x b).1 hb.1, (e₁ b).1 hb.2⟩]
  rfl

theorem exists_basis_image {c : Coeff l} [Algebra c.F Ω] (h : IsLinHom Ψ) [Etale Ψ] {p : ℕ} (hp : (p : Ω) ≠ 0)
    (τ : E →+* ℂ) {m : ℕ} (u : Fin m → (Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left)) (tan : ∀ i, IsTanAt x (u i))
    (eig : ∀ i, IsEigAt c τ (u i))
    (basis : ∀ w, IsTanAt x w → IsEigAt c τ w → ∃! a : Fin m → Ω, IsCombAt x u a w) :
    ∃ u' : Fin m → (Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left), (∀ i, IsLieImg p Ψ (u i) (u' i)) ∧
      (∀ i, IsEigAt c τ (u' i)) ∧ ∀ w, IsTanAt x' w → IsEigAt c τ w → ∃! a : Fin m → Ω, IsCombAt x' u' a w := by
  obtain ⟨a, rfl⟩ : ∃ a : Fin m → (tEps x ⟶ Xo.univ.t.G), u = fun i => (a i).left :=
    ⟨fun i => Over.homMk (u i) (tan i).1, rfl⟩
  let q : Ω := (p : Ω)⁻¹
  have c₁ : ∀ y : Sp Ω ⟶ Xo.X, scaleAt y q ≫ scaleAt y p = 𝟙 _ := fun y =>
    Over.OverMorphism.ext (eps_cancel (inv_mul_cancel₀ hp))
  have c₂ : ∀ y : Sp Ω ⟶ Xo.X, scaleAt y p ≫ scaleAt y q = 𝟙 _ := fun y =>
    Over.OverMorphism.ext (eps_cancel (mul_inv_cancel₀ hp))
  let L : (tEps x ⟶ Xo.univ.t.G) →* (tEps x' ⟶ Xo.univ.t.G) :=
    MonoidHom.mk' (fun b => scaleAt x' q ≫ tanMap h b) fun b b' => by rw [map_mul, MonObj.comp_mul]
  have hL : ∀ b, L b = scaleAt x' q ≫ tanMap h b := fun _ => rfl
  have zs : ∀ (y : Sp Ω ⟶ Xo.X) (s : Ω) (b : tEps y ⟶ Xo.univ.t.G), zeroAt y ≫ b = 1 →
      zeroAt y ≫ scaleAt y s ≫ b = 1 := fun y s b hb => by rw [← Category.assoc, zeroAt_scaleAt, hb]
  have Lz : ∀ b, zeroAt x ≫ b = 1 → zeroAt x' ≫ L b = 1 := fun b hb => zs _ _ _ (tanMap_zero h hb)
  have Ls : ∀ s b, L (scaleAt x s ≫ b) = scaleAt x' s ≫ L b := fun s b => by
    rw [hL, hL, tanMap_scale, ← Category.assoc, scaleAt_comm, Category.assoc]
  have La : ∀ r b, L (b ≫ Xo.univ.t.act.act r) = L b ≫ Xo.univ.t.act.act r := fun r b => by
    rw [hL, hL, tanMap_act, Category.assoc]
  have Li : ∀ b b', zeroAt x ≫ b = 1 → zeroAt x ≫ b' = 1 → L b = L b' → b = b' := fun b b' hb hb' e => by
    have e' := congrArg (scaleAt x' p ≫ ·) e
    simp only [hL, reassoc_of% (c₂ x')] at e'
    exact (existsUnique_tanMap h (tanMap_zero h hb')).unique ⟨hb, e'⟩ ⟨hb', rfl⟩
  have ta : ∀ i, zeroAt x ≫ a i = 1 := fun i => (isTanAt_iff _).1 (tan i)
  refine ⟨fun i => (L (a i)).left, fun i => ⟨tan i, (isTanAt_iff _).2 (Lz _ (ta i)), a i, rfl, ?_⟩,
    fun i => (isEigAt_iff τ _).2 fun r => ?_, fun w hw hw' => ?_⟩
  · exact congrArg (·.left) (show scaleAt x' p ≫ L (a i) = tanMap h (a i) by rw [hL, reassoc_of% (c₂ x')])
  · rw [← La, (isEigAt_iff τ _).1 (eig i), Ls]
  · obtain ⟨w, rfl⟩ : ∃ b : tEps x' ⟶ Xo.univ.t.G, w = b.left := ⟨Over.homMk w hw.1, rfl⟩
    obtain ⟨v, ⟨hv, e⟩, -⟩ := existsUnique_tanMap h (zs x' p w ((isTanAt_iff _).1 hw))
    obtain rfl : L v = w := by rw [hL, e, reassoc_of% (c₁ x')]
    have ev : IsEigAt c τ v.left := (isEigAt_iff τ _).2 fun r => Li _ _
      (by have := Xo.univ.t.act.hom r; rw [← Category.assoc, hv, MonObj.one_comp]) (zs _ _ _ hv)
      (by rw [La, Ls, (isEigAt_iff τ _).1 hw'])
    refine (existsUnique_congr fun cf => ?_).1 (basis _ ((isTanAt_iff _).2 hv) ev)
    have e : L (List.ofFn fun i => scaleAt x (cf i) ≫ a i).prod =
        (List.ofFn fun i => scaleAt x' (cf i) ≫ L (a i)).prod := by
      rw [map_list_prod, List.map_ofFn]
      exact congrArg (fun f => (List.ofFn f).prod) (funext fun i => Ls _ _)
    rw [isCombAt_iff, isCombAt_iff, ← e]
    refine ⟨congrArg L, Li _ _ (LieEtale.comp_listProd _ _ fun b hb => ?_) hv⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hb
    exact zs _ _ _ (ta i)

end Lie

section Points

variable {c : Coeff l} {P : Ideal (𝓞 E)} {p i : ℕ}

theorem exists_hkRelFr (h : IsSplitOff l P p) {tr : Transport Xo c} (ht : TrTotal Xo c tr P p i) (Ω : Type) [Field Ω]
    [IsAlgClosed Ω] [Algebra c.F Ω] (y : FrPt Xo c Ω) (C : hkKer (Xo := Xo) P p i Ω y) :
    ∃ z, hkRelFr P p i (ofTransport tr) Ω y C z := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap c.F Ω).injective
  obtain ⟨x', ψ, f, hψ, -, het, -⟩ := exists_etale_isHkIsog Xo h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 y.x C.1 C.2
  have hΨ := (isog_iff ((Nat.Prime.coprime_iff_not_dvd h.2.2.1).2 h.2.2.2.2) _ _ _ _).1 ⟨f, hψ⟩
  have : Etale (conj y.x x' ψ) := by rw [conj_apply]; infer_instance
  obtain ⟨s', hs', htr⟩ := ht Ω y.x x' C.1 _ y.s y.x_over C.2 hΨ y.gen
  choose u' h₁ h₂ h₃ using fun τ => exists_basis_image (c := c) hΨ.2.1 (Nat.cast_ne_zero.2 h.2.2.1.ne_zero) τ
    (y.u τ) (y.tan τ) (y.eig τ) (y.basis τ)
  exact ⟨⟨x', hψ.1.trans y.x_over, u', fun τ j => (h₁ τ j).2.1, h₂, h₃, s', hs'⟩,
    (hkRelFr_ofTransport_iff h i tr Ω y C _).2 ⟨_, hΨ, h₁, htr⟩⟩

theorem hkRelFr_unique (h : IsSplitOff l P p) {tr : Transport Xo c} (ht : TrUnique Xo c tr P p i) (Ω : Type) [Field Ω]
    [IsAlgClosed Ω] [Algebra c.F Ω] (y : FrPt Xo c Ω) (C : hkKer (Xo := Xo) P p i Ω y) (z z' : FrPt Xo c Ω)
    (hz : hkRelFr P p i (ofTransport tr) Ω y C z) (hz' : hkRelFr P p i (ofTransport tr) Ω y C z') : z = z' := by
  obtain ⟨ψ, f, hψ, hu, hs⟩ := hz
  obtain ⟨ψ', f', hψ', hu', hs'⟩ := hz'
  obtain ⟨-, k₁, k₂⟩ := isHkIsog_etale_unique Xo h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 C.2 hψ
  obtain ⟨x, xo, u, ta, ei, ba, s, ge⟩ := z
  obtain ⟨x', xo', u', ta', ei', ba', s', ge'⟩ := z'
  obtain rfl : x' = x := k₁ _ _ _ hψ'
  obtain rfl : ψ' = ψ := k₂ _ _ hψ'
  obtain rfl : u = u' := funext fun τ => funext fun j => by
    obtain ⟨w₁, a₁, b₁, e₁⟩ := hu τ j
    obtain ⟨w₂, a₂, b₂, e₂⟩ := hu' τ j
    obtain rfl : w₁ = w₂ := pullback.hom_ext (a₁.trans a₂.symm) (b₁.trans b₂.symm)
    exact e₁.trans e₂.symm
  obtain rfl : s = s' := ht Ω y.x x' C.1 _ y.s s s' y.x_over C.2
    ((isog_iff ((Nat.Prime.coprime_iff_not_dvd h.2.2.1).2 h.2.2.2.2) _ _ _ _).1 ⟨f, hψ⟩) y.gen ge ge' hs hs'
  rfl

end Points

def ThetaTransportLaw : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ), IsSplitOff l P p →
    TrTotal Xo c (thetaTransport Xo c p) P p i ∧ TrUnique Xo c (thetaTransport Xo c p) P p i

theorem heckeFinite : HeckeFinite := fun _ _ _ _ _ _ _ _ _ _ _ i h _ _ _ _ y =>
  finite_heckeKer h.2.2.2.1.pos h.2.2.2.2 i y.x

theorem pointsDetect : PointsDetect := Frames.ptsDetect_framed

theorem heckePointLaws_of_transport (hT : ThetaTransportLaw) : HeckePointLaws :=
  ⟨heckeFinite,
    fun E _ _ _ H Dw l Xo c P p i h => exists_hkRelFr (isHeckePrime_iff.1 h)
      (hT E H Dw l Xo c P p i (isHeckePrime_iff.1 h)).1,
    fun E _ _ _ H Dw l Xo c P p i h Ω _ _ _ y C z z' hz hz' => by
      obtain rfl := hkRelFr_unique (isHeckePrime_iff.1 h) (hT E H Dw l Xo c P p i (isHeckePrime_iff.1 h)).2
        Ω y C z z' hz hz'
      exact Frames.frMapUniq_refl z,
    pointsDetect⟩

end GlobalTheory.HeckePointLaw
