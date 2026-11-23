import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfMain

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar.BT
  GlobalTheory.CompanionTheory.Ar.BT.SubOrder PositivityTheory.HtPt.Twhopf

noncomputable section

namespace PositivityTheory.HtPt.Gi

section Pts

variable {Z : Scheme.{0}} {W : Over Z} {U : W.left.Opens} (hU : IsAffineOpen U)

abbrev affOver : Over Z := Over.mk (hU.fromSpec ≫ W.hom)

def taut : affOver hU ⟶ W := Over.homMk hU.fromSpec rfl

theorem taut_mem : ⊤ ≤ (taut hU).left ⁻¹ᵁ U := (top_le_iff_mem _ _).2 (fromSpec_mem hU)

theorem val_taut (h : ⊤ ≤ (taut hU).left ⁻¹ᵁ U) (s : Γ(W.left, U)) :
    valHom (B := Γ(W.left, U)) (taut hU).left U h s = s := by
  have e := spec_valHom_fromSpec (B := Γ(W.left, U)) (taut hU).left hU h
  have e2 : Spec.map (CommRingCat.ofHom (valHom (B := Γ(W.left, U)) (taut hU).left U h)) = Spec.map (𝟙 _) := by
    rw [← cancel_mono hU.fromSpec, e, Spec.map_id, Category.id_comp]
    rfl
  exact congrArg (fun f => f.hom s) (Spec.map_injective e2)

def fac {B : Type} [CommRing B] {f : Spec (CommRingCat.of B) ⟶ Z} (z : Over.mk f ⟶ W) (h : ⊤ ≤ z.left ⁻¹ᵁ U) :
    Over.mk f ⟶ affOver hU :=
  Over.homMk (Spec.map (CommRingCat.ofHom (valHom (B := B) z.left U h))) (by
    have e := spec_valHom_fromSpec (B := B) z.left hU h
    change _ ≫ hU.fromSpec ≫ W.hom = f
    rw [← Category.assoc]
    exact (congrArg (· ≫ W.hom) e).trans (Over.w z))

theorem fac_taut {B : Type} [CommRing B] {f : Spec (CommRingCat.of B) ⟶ Z} (z : Over.mk f ⟶ W)
    (h : ⊤ ≤ z.left ⁻¹ᵁ U) : fac hU z h ≫ taut hU = z :=
  Over.OverMorphism.ext (spec_valHom_fromSpec (B := B) z.left hU h)

include hU in

theorem val_comp {B C : Type} [CommRing B] [CommRing C] {f : Spec (CommRingCat.of B) ⟶ Z}
    {g : Spec (CommRingCat.of C) ⟶ Z} (q : Over.mk g ⟶ Over.mk f) (φ : B →+* C)
    (hq : q.left = Spec.map (CommRingCat.ofHom φ)) (a : Over.mk f ⟶ W) (h : ⊤ ≤ a.left ⁻¹ᵁ U)
    (b : Over.mk g ⟶ W) (hb : b = q ≫ a) (h' : ⊤ ≤ b.left ⁻¹ᵁ U) (s : Γ(W.left, U)) :
    valHom (B := C) b.left U h' s = φ (valHom (B := B) a.left U h s) := by
  have e : b.left = Spec.map (CommRingCat.ofHom φ) ≫ a.left := by rw [hb, Over.comp_left, hq]
  exact (DFunLike.congr_fun (valHom_congr (B := C) e U h' (e ▸ h')) s).trans
    (valHom_comp (B := B) a.left hU h φ _ s)

theorem comp_mem {Y Y' : Over Z} (q : Y' ⟶ Y) (a : Y ⟶ W) (h : ⊤ ≤ a.left ⁻¹ᵁ U) (b : Y' ⟶ W) (hb : b = q ≫ a) :
    ⊤ ≤ b.left ⁻¹ᵁ U := by
  subst hb
  exact fun z _ => h (Set.mem_univ (q.left z))

theorem val_fac {W' : Over Z} {U' : W'.left.Opens} (hU' : IsAffineOpen U') (k : affOver hU ⟶ W')
    (hk : ⊤ ≤ k.left ⁻¹ᵁ U') {B : Type} [CommRing B] {f : Spec (CommRingCat.of B) ⟶ Z} (z : Over.mk f ⟶ W)
    (h : ⊤ ≤ z.left ⁻¹ᵁ U) (b : Over.mk f ⟶ W') (hb : b = fac hU z h ≫ k) :
    ∃ h', ∀ s, valHom (B := B) b.left U' h' s =
      valHom (B := B) z.left U h (valHom (B := Γ(W.left, U)) k.left U' hk s) :=
  ⟨comp_mem _ k hk b hb, fun s => val_comp (B := Γ(W.left, U)) hU' (fac hU z h) _ rfl k hk b hb _ s⟩

include hU in

theorem pt_ext {B : Type} [CommRing B] {f : Spec (CommRingCat.of B) ⟶ Z} (a b : Over.mk f ⟶ W)
    (ha : ⊤ ≤ a.left ⁻¹ᵁ U) (hb : ⊤ ≤ b.left ⁻¹ᵁ U)
    (h : ∀ s, valHom (B := B) a.left U ha s = valHom (B := B) b.left U hb s) : a = b := by
  apply Over.OverMorphism.ext
  have e1 := spec_valHom_fromSpec (B := B) a.left hU ha
  have e2 := spec_valHom_fromSpec (B := B) b.left hU hb
  rw [RingHom.ext h] at e1
  exact e1.symm.trans e2

theorem val_congr {B : Type} [CommRing B] {f : Spec (CommRingCat.of B) ⟶ Z} {a b : Over.mk f ⟶ W} (e : a = b)
    (ha : ⊤ ≤ a.left ⁻¹ᵁ U) (hb : ⊤ ≤ b.left ⁻¹ᵁ U) (s : Γ(W.left, U)) :
    valHom (B := B) a.left U ha s = valHom (B := B) b.left U hb s := by
  subst e; rfl

theorem affOver_finite (h : IsFinite (U.ι ≫ W.hom)) : IsFinite (affOver hU).hom := by
  change IsFinite (hU.fromSpec ≫ W.hom)
  rw [← hU.isoSpec_inv_ι, Category.assoc]
  infer_instance

end Pts

variable {R : Type} [CommRing R] [IsLocalRing R] {W W' : Over (Spec (CommRingCat.of R))} [GrpObj W']

set_option maxHeartbeats 400000 in

theorem core {N : ℕ} (j : W ⟶ W') (hinj : ∀ (Y) (y y' : Y ⟶ W), y ≫ j = y' ≫ j → y = y')
    (hker : ∀ (Y) (z : Y ⟶ W'), z ^ N = 1 ↔ ∃ y, y ≫ j = z) (U : W.left.Opens) (U' : W'.left.Opens)
    (hF : IsFinite (U.ι ≫ W.hom)) (hF' : IsFinite (U'.ι ≫ W'.hom))
    (hU : ∀ x : W.left, W.hom x = IsLocalRing.closedPoint R → x ∈ U)
    (hU' : ∀ x : W'.left, W'.hom x = IsLocalRing.closedPoint R → x ∈ U') :
    ∃ r : Γ(W'.left, U') →+* Γ(W.left, U), Function.Surjective r ∧
      (∀ (z : genPt R ⟶ W) h, ∃ h', ∀ s, valAt z.left U h (r s) = valAt (z ≫ j).left U' h' s) ∧
      ∀ I : Ideal Γ(W'.left, U'), (∀ s c, (∀ (z : genPt R ⟶ W') h, ∃ hN h1, valAt z.left U' h c =
        valAt (z ^ N).left U' hN s - valAt (1 : genPt R ⟶ W').left U' h1 s) → c ∈ I) → RingHom.ker r ≤ I := by
  have hA : IsAffineOpen U := isAffine_of_isAffineHom (U.ι ≫ W.hom)
  have hA' : IsAffineOpen U' := isAffine_of_isAffineHom (U'.ι ≫ W'.hom)
  have hY := affOver_finite hA hF
  have hY' := affOver_finite hA' hF'
  have m1 : ∀ a : affOver hA ⟶ W', ⊤ ≤ a.left ⁻¹ᵁ U' := fun a z _ => mem_of_finite U' hU' _ hY a z
  have m2 : ∀ a : affOver hA' ⟶ W', ⊤ ≤ a.left ⁻¹ᵁ U' := fun a z _ => mem_of_finite U' hU' _ hY' a z
  let r : Γ(W'.left, U') →+* Γ(W.left, U) := valHom (B := Γ(W.left, U)) (taut hA ≫ j).left U' (m1 _)
  have hr : ∀ {B : Type} [CommRing B] {f : Spec (CommRingCat.of B) ⟶ _} (z : Over.mk f ⟶ W) h,
      ∃ h', ∀ s, valHom (B := B) z.left U h (r s) = valHom (B := B) (z ≫ j).left U' h' s := by
    intro B _ f z h
    have e : z ≫ j = fac hA z h ≫ taut hA ≫ j := by rw [← Category.assoc, fac_taut]
    obtain ⟨h', e'⟩ := val_fac hA hA' _ (m1 _) z h _ e
    exact ⟨h', fun s => (e' s).symm⟩
  let δ : Γ(W'.left, U') → Γ(W'.left, U') := fun s =>
    valHom (B := Γ(W'.left, U')) (taut hA' ^ N).left U' (m2 _) s -
      valHom (B := Γ(W'.left, U')) (1 : affOver hA' ⟶ W').left U' (m2 _) s
  have hδ : ∀ {B : Type} [CommRing B] {f : Spec (CommRingCat.of B) ⟶ _} (z : Over.mk f ⟶ W') h,
      ∃ hN h1, ∀ s, valHom (B := B) z.left U' h (δ s) =
        valHom (B := B) (z ^ N).left U' hN s - valHom (B := B) (1 : Over.mk f ⟶ W').left U' h1 s := by
    intro B _ f z h
    have e : z ^ N = fac hA' z h ≫ taut hA' ^ N := by rw [MonObj.comp_pow, fac_taut]
    have e1 : (1 : Over.mk f ⟶ W') = fac hA' z h ≫ 1 := (MonObj.comp_one _).symm
    obtain ⟨hN, eN⟩ := val_fac hA' hA' _ (m2 _) z h _ e
    obtain ⟨h1, e1⟩ := val_fac hA' hA' _ (m2 _) z h _ e1
    exact ⟨hN, h1, fun s => (map_sub _ _ _).trans (congrArg₂ (· - ·) (eN s).symm (e1 s).symm)⟩
  let I₀ : Ideal Γ(W'.left, U') := Ideal.span (Set.range δ)
  let π := Ideal.Quotient.mk I₀
  let f₀ := Spec.map (CommRingCat.ofHom π) ≫ hA'.fromSpec ≫ W'.hom
  let q : Over.mk f₀ ⟶ affOver hA' := Over.homMk (Spec.map (CommRingCat.ofHom π)) rfl
  have hf₀ : IsFinite (Over.mk f₀).hom := by
    have : IsFinite (Spec.map (CommRingCat.ofHom π)) :=
      (IsFinite.SpecMap_iff _).2 (RingHom.Finite.of_surjective π Ideal.Quotient.mk_surjective)
    have : IsFinite (hA'.fromSpec ≫ W'.hom) := hY'
    exact inferInstanceAs (IsFinite (Spec.map (CommRingCat.ofHom π) ≫ hA'.fromSpec ≫ W'.hom))
  have hqm := comp_mem q _ (taut_mem hA') _ rfl
  have hq : ∀ s, valHom (B := _ ⧸ I₀) (q ≫ taut hA').left U' hqm s = π s := fun s => by
    rw [val_comp (B := Γ(W'.left, U')) hA' q π rfl _ (taut_mem hA') _ rfl _ s, val_taut]
  have hqN : (q ≫ taut hA') ^ N = 1 := by
    obtain ⟨hN, h1, e⟩ := hδ (q ≫ taut hA') hqm
    refine pt_ext hA' _ _ hN h1 fun s => ?_
    rw [← sub_eq_zero, ← e, hq]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨s, rfl⟩)
  obtain ⟨y, hy⟩ := (hker _ _).1 hqN
  have hym : ⊤ ≤ y.left ⁻¹ᵁ U := fun z _ => mem_of_finite U hU _ hf₀ y z
  have hyr : ∀ s, valHom (B := _ ⧸ I₀) y.left U hym (r s) = π s := fun s => by
    obtain ⟨h', e⟩ := hr (B := _ ⧸ I₀) (f := f₀) y hym
    exact (e s).trans ((val_congr hy h' hqm s).trans (hq s))
  refine ⟨r, fun s => ?_, fun z h => hr z h, fun I hI s hs => ?_⟩
  · have h0 : ∀ a ∈ I₀, r a = 0 := by
      intro a ha
      refine (show I₀ ≤ RingHom.ker r from Ideal.span_le.2 ?_) ha
      rintro _ ⟨t, rfl⟩
      obtain ⟨hN, h1, e⟩ := hδ (B := Γ(W.left, U)) (taut hA ≫ j) (m1 _)
      have e1 : (taut hA ≫ j) ^ N = 1 := (hker _ _).2 ⟨_, rfl⟩
      refine (e t).trans (sub_eq_zero.2 ?_)
      exact val_congr (B := Γ(W.left, U)) e1 hN h1 t
    let rb := Ideal.Quotient.lift I₀ r h0
    have e0 : Spec.map (CommRingCat.ofHom rb) ≫ Spec.map (CommRingCat.ofHom π) = Spec.map (CommRingCat.ofHom r) := by
      rw [← Spec.map_comp]
      rfl
    let v : affOver hA ⟶ Over.mk f₀ := Over.homMk (Spec.map (CommRingCat.ofHom rb)) (by
      change _ ≫ Spec.map (CommRingCat.ofHom π) ≫ _ = _
      rw [← Category.assoc, e0]
      exact Over.w (fac (B := Γ(W.left, U)) hA' (taut hA ≫ j) (m1 _)))
    have e1 : v ≫ q = fac (B := Γ(W.left, U)) hA' (taut hA ≫ j) (m1 _) := Over.OverMorphism.ext e0
    have e2 : taut hA = v ≫ y := hinj _ _ _ (by
      rw [Category.assoc, hy, ← Category.assoc, e1, fac_taut])
    have e3 := val_comp (C := Γ(W.left, U)) hA v rb rfl y hym _ e2 (taut_mem hA) s
    rw [val_taut] at e3
    obtain ⟨s', hs'⟩ := Ideal.Quotient.mk_surjective (valHom (B := _ ⧸ I₀) y.left U hym s)
    exact ⟨s', by rw [e3, ← hs']; rfl⟩
  · have h1 : s ∈ I₀ := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      have := hyr s
      rw [(RingHom.mem_ker).1 hs, map_zero] at this
      exact this.symm
    refine (show I₀ ≤ I from Ideal.span_le.2 ?_) h1
    rintro _ ⟨t, rfl⟩
    refine hI t _ fun z h => ?_
    obtain ⟨hN, h1, e⟩ := hδ z h
    exact ⟨hN, h1, e t⟩

end PositivityTheory.HtPt.Gi
