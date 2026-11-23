import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HkRelFrOfTransportIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueTangentLift
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckePointLawRing

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori GlobalTheory.HeckeFrCompare

attribute [local instance] Over.cartesianMonoidalCategory

theorem existsUnique_dual_lift {X Y : Scheme.{0}} (f : X ⟶ Y) [Etale f] {T : Type} [CommRing T]
    (s : Sp (DualNumber T) ⟶ Y) (x₀ : Sp T ⟶ X)
    (h : x₀ ≫ f = spMap (TrivSqZeroExt.fstHom T T T).toRingHom ≫ s) :
    ∃! x : Sp (DualNumber T) ⟶ X,
      spMap (TrivSqZeroExt.fstHom T T T).toRingHom ≫ x = x₀ ∧ x ≫ f = s := by
  let π : CommRingCat.of (DualNumber T) ⟶ CommRingCat.of T :=
    CommRingCat.ofHom (TrivSqZeroExt.fstHom T T T).toRingHom
  have hπ : Function.Surjective π := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hsq : ∀ a b : DualNumber T, a.fst = 0 → b.fst = 0 → a * b = 0 := fun a b ha hb => by
    ext <;> simp [ha, hb]
  have hnil : IsNilpotent (RingHom.ker π.hom) :=
    ⟨2, by
      rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
      exact fun a ha b hb => hsq a b ha hb⟩
  exact GlobalTheory.existsUnique_lift_of_etale_of_surjective f π hπ hnil x₀ s h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

variable {T : Type} [CommRing T]

abbrev epsBase (T : Type) [CommRing T] : Sp (DualNumber T) ⟶ Sp T := spMap (algebraMap T (DualNumber T))

abbrev epsZero (T : Type) [CommRing T] : Sp T ⟶ Sp (DualNumber T) := spMap (TrivSqZeroExt.fstHom T T T).toRingHom

theorem spMap_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem epsZero_base : epsZero T ≫ epsBase T = 𝟙 _ := by
  rw [spMap_spMap]
  exact (congrArg spMap (RingHom.ext fun _ => rfl)).trans (Spec.map_id _)

theorem eps_base (a : T) : spMap (epsMul a) ≫ epsBase T = epsBase T := by
  rw [spMap_spMap]
  refine congrArg spMap (RingHom.ext fun r => ?_)
  ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem epsZero_eps (a : T) : epsZero T ≫ spMap (epsMul a) = epsZero T := by
  rw [spMap_spMap]
  refine congrArg spMap (RingHom.ext fun r => ?_)
  simp [epsMul]

theorem eps_comm (a b : T) : spMap (epsMul a) ≫ spMap (epsMul b) = spMap (epsMul b) ≫ spMap (epsMul a) := by
  rw [spMap_spMap, spMap_spMap]
  refine congrArg spMap (RingHom.ext fun r => ?_)
  ext <;> simp [epsMul, mul_left_comm]

theorem eps_cancel {a b : T} (h : a * b = 1) : spMap (epsMul a) ≫ spMap (epsMul b) = 𝟙 _ := by
  have : (epsMul a).comp (epsMul b) = RingHom.id _ := by
    refine RingHom.ext fun x => ?_
    ext <;> simp [epsMul, ← _root_.mul_assoc, h]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, this]
  exact Spec.map_id _

abbrev zeroAt (x : Sp T ⟶ Xo.X) : (Over.mk x : Over Xo.X) ⟶ tEps x := sec' x (epsZero T) epsZero_base

abbrev scaleAt (x : Sp T ⟶ Xo.X) (a : T) : tEps x ⟶ tEps x := res x (spMap (epsMul a)) (eps_base a)

theorem zeroAt_scaleAt (x : Sp T ⟶ Xo.X) (a : T) : zeroAt x ≫ scaleAt x a = zeroAt x :=
  Over.OverMorphism.ext (epsZero_eps a)

theorem scaleAt_comm (x : Sp T ⟶ Xo.X) (a b : T) : scaleAt x a ≫ scaleAt x b = scaleAt x b ≫ scaleAt x a :=
  Over.OverMorphism.ext (eps_comm a b)

theorem isTanAt_iff {x : Sp T ⟶ Xo.X} (a : tEps x ⟶ Xo.univ.t.G) : IsTanAt x a.left ↔ zeroAt x ≫ a = 1 :=
  ⟨fun h => Over.OverMorphism.ext h.2, fun h => ⟨Over.w a, congrArg (·.left) h⟩⟩

theorem isEigAt_iff {c : Coeff l} [Algebra c.F T] {x : Sp T ⟶ Xo.X} (τ : E →+* ℂ) (a : tEps x ⟶ Xo.univ.t.G) :
    IsEigAt c τ a.left ↔ ∀ r : 𝓞 E, a ≫ Xo.univ.t.act.act r = scaleAt x (algebraMap c.F T (embK c τ r)) ≫ a :=
  forall_congr' fun _ => ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg (·.left) h⟩

theorem isCombAt_iff {x : Sp T ⟶ Xo.X} {m : ℕ} (a : Fin m → (tEps x ⟶ Xo.univ.t.G)) (cf : Fin m → T)
    (b : tEps x ⟶ Xo.univ.t.G) :
    IsCombAt x (fun i => (a i).left) cf b.left ↔ (List.ofFn fun i => scaleAt x (cf i) ≫ a i).prod = b := by
  constructor
  · rintro ⟨u, hu, h⟩
    obtain rfl : u = fun i => scaleAt x (cf i) ≫ a i := funext fun i => Over.OverMorphism.ext (hu i)
    exact Over.OverMorphism.ext h
  · intro h
    exact ⟨_, fun _ => rfl, congrArg (·.left) h⟩

variable {x x' : Sp T ⟶ Xo.X} {Ψ : Gx x ⟶ Gx x'}

def tanMap (h : IsLinHom Ψ) : (tEps x ⟶ Xo.univ.t.G) →* (tEps x' ⟶ Xo.univ.t.G) :=
  MonoidHom.mk' (fun a => Over.homMk (push Ψ (epsBase T) a) (push_hom h.1 _ a)) fun a b =>
    Over.OverMorphism.ext (h.2.1 _ _ a b _ _ rfl rfl).symm

theorem tanMap_left (h : IsLinHom Ψ) (a : tEps x ⟶ Xo.univ.t.G) : (tanMap h a).left = push Ψ (epsBase T) a := rfl

theorem tanMap_scale (h : IsLinHom Ψ) (s : T) (a : tEps x ⟶ Xo.univ.t.G) :
    tanMap h (scaleAt x s ≫ a) = scaleAt x' s ≫ tanMap h a :=
  Over.OverMorphism.ext (push_res Ψ _ _ a)

theorem tanMap_act (h : IsLinHom Ψ) (r : 𝓞 E) (a : tEps x ⟶ Xo.univ.t.G) :
    tanMap h (a ≫ Xo.univ.t.act.act r) = tanMap h a ≫ Xo.univ.t.act.act r := by
  refine Over.OverMorphism.ext ?_
  have e : toFib x (epsBase T) (a ≫ Xo.univ.t.act.act r) =
      toFib x (epsBase T) a ≫ (Over.mk x ◁ Xo.univ.t.act.act r).left := by
    rw [toFib, toFib, ← Over.comp_left, lift_whiskerLeft]
  rw [Over.comp_left, tanMap_left, tanMap_left, push, push, e, Category.assoc, reassoc_of% (h.2.2 r),
    ← Over.comp_left, whiskerLeft_snd, Over.comp_left]
  simp only [Category.assoc]

theorem sends_one (h : IsLinHom Ψ) : Sends Ψ 1 1 := by
  obtain ⟨f, hf, -⟩ := exists_pointHom h
  simpa using hf 1

theorem tanMap_zero (h : IsLinHom Ψ) {a : tEps x ⟶ Xo.univ.t.G} (ha : zeroAt x ≫ a = 1) :
    zeroAt x' ≫ tanMap h a = 1 :=
  Over.OverMorphism.ext ((sends_sec'_iff h.1 (epsZero T) epsZero_base a 1).1 (by rw [ha]; exact sends_one h))

theorem existsUnique_tanMap (h : IsLinHom Ψ) [Etale Ψ] {w : tEps x' ⟶ Xo.univ.t.G} (hw : zeroAt x' ≫ w = 1) :
    ∃! a : tEps x ⟶ Xo.univ.t.G, zeroAt x ≫ a = 1 ∧ tanMap h a = w := by
  have e₀ : ∀ (y : Sp T ⟶ Xo.X) (a : tEps y ⟶ Xo.univ.t.G), zeroAt y ≫ a = 1 ↔
      epsZero T ≫ toFib y (epsBase T) a = (lift (𝟙 (Over.mk y)) (1 : Over.mk y ⟶ Xo.univ.t.G)).left := fun y a => by
    rw [← lift_sec' y _ epsZero_base]
    refine ⟨fun e => by rw [← e], fun e => Over.OverMorphism.ext ?_⟩
    rw [← lift_l_snd (𝟙 (Over.mk y)) (_ ≫ a), e, lift_l_snd]
  have e₁ : ∀ a : tEps x ⟶ Xo.univ.t.G, tanMap h a = w ↔ toFib x (epsBase T) a ≫ Ψ = toFib x' (epsBase T) w :=
    fun a => by
      refine ⟨fun e => gx_ext ?_ ?_, fun e => Over.OverMorphism.ext ?_⟩
      · rw [Category.assoc, h.1, toFib_fst, toFib_fst]
      · rw [toFib_snd, ← e, tanMap_left, push, Category.assoc]
      · rw [tanMap_left, push, reassoc_of% e, toFib_snd]
  obtain ⟨v, ⟨h₁, h₂⟩, hu⟩ := existsUnique_dual_lift Ψ (toFib x' (epsBase T) w)
    (lift (𝟙 (Over.mk x)) (1 : Over.mk x ⟶ Xo.univ.t.G)).left ((sends_one h).trans ((e₀ x' w).1 hw).symm)
  have hv : v ≫ (fst (Over.mk x) Xo.univ.t.G).left = epsBase T := by rw [← h.1, reassoc_of% h₂, toFib_fst]
  let a : tEps x ⟶ Xo.univ.t.G := Over.homMk (v ≫ (snd (Over.mk x) Xo.univ.t.G).left) (by
    rw [Category.assoc, snd_hom, reassoc_of% hv]; rfl)
  have ha : toFib x (epsBase T) a = v := gx_ext (by rw [toFib_fst, hv]) (by rw [toFib_snd]; rfl)
  refine ⟨a, ⟨(e₀ x a).2 (by rw [ha, h₁]), (e₁ a).2 (by rw [ha, h₂])⟩, fun b hb => Over.OverMorphism.ext ?_⟩
  rw [← toFib_snd x _ b, hu _ ⟨(e₀ x b).1 hb.1, (e₁ b).1 hb.2⟩]
  rfl

theorem exists_basis_image {c : Coeff l} [Algebra c.F T] (h : IsLinHom Ψ) [Etale Ψ] {p : ℕ} {q : T}
    (hq : q * p = 1) (τ : E →+* ℂ) {m : ℕ} (u : Fin m → (Sp (DualNumber T) ⟶ Xo.univ.t.G.left))
    (tan : ∀ i, IsTanAt x (u i)) (eig : ∀ i, IsEigAt c τ (u i))
    (basis : ∀ w, IsTanAt x w → IsEigAt c τ w → ∃! a : Fin m → T, IsCombAt x u a w) :
    ∃ u' : Fin m → (Sp (DualNumber T) ⟶ Xo.univ.t.G.left), (∀ i, IsLieImg p Ψ (u i) (u' i)) ∧
      (∀ i, IsEigAt c τ (u' i)) ∧ ∀ w, IsTanAt x' w → IsEigAt c τ w → ∃! a : Fin m → T, IsCombAt x' u' a w := by
  obtain ⟨a, rfl⟩ : ∃ a : Fin m → (tEps x ⟶ Xo.univ.t.G), u = fun i => (a i).left :=
    ⟨fun i => Over.homMk (u i) (tan i).1, rfl⟩
  have c₁ : ∀ y : Sp T ⟶ Xo.X, scaleAt y q ≫ scaleAt y p = 𝟙 _ := fun y =>
    Over.OverMorphism.ext (eps_cancel hq)
  have c₂ : ∀ y : Sp T ⟶ Xo.X, scaleAt y p ≫ scaleAt y q = 𝟙 _ := fun y =>
    Over.OverMorphism.ext (eps_cancel ((mul_comm _ _).trans hq))
  let L : (tEps x ⟶ Xo.univ.t.G) →* (tEps x' ⟶ Xo.univ.t.G) :=
    MonoidHom.mk' (fun b => scaleAt x' q ≫ tanMap h b) fun b b' => by rw [map_mul, MonObj.comp_mul]
  have hL : ∀ b, L b = scaleAt x' q ≫ tanMap h b := fun _ => rfl
  have zs : ∀ (y : Sp T ⟶ Xo.X) (s : T) (b : tEps y ⟶ Xo.univ.t.G), zeroAt y ≫ b = 1 →
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

end GlobalTheory.HeckePointLawRing

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

theorem GlobalTheory.HeckePointLawRing.exists_frame_image : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : Type) [CommRing T] [Algebra c.F T]
    (y : FrPt Xo c T) (x' : Sp T ⟶ Xo.X) (Ψ : Gx y.x ⟶ Gx x') (p : ℕ), p ≠ 0 → IsLinHom Ψ → Etale Ψ →
    ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T) ⟶ Xo.univ.t.G.left),
      (∀ τ j, IsLieImg p Ψ (y.u τ j) (u τ j)) ∧ (∀ τ j, IsEigAt c τ (u τ j)) ∧
      ∀ τ w, IsTanAt x' w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → T, IsCombAt x' (u τ) a w := by
  intro E _ _ _ H Dw l Xo c T _ _ y x' Ψ p hp h het
  have hF : ((p : c.F)) ≠ 0 := Nat.cast_ne_zero.2 hp
  have hq : algebraMap c.F T ((p : c.F)⁻¹) * (p : T) = 1 := by
    rw [← map_natCast (algebraMap c.F T) p, ← map_mul, inv_mul_cancel₀ hF, map_one]
  choose u h₁ h₂ h₃ using fun τ => GlobalTheory.HeckePointLawRing.exists_basis_image (c := c) h hq τ
    (y.u τ) (y.tan τ) (y.eig τ) (y.basis τ)
  exact ⟨u, h₁, h₂, h₃⟩
