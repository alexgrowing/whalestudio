import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineOpenInfOfIsSeparated
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechInv

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {J : Type}

def pairOpen (V : J → A.left.Opens) (t : J × J × J) : (A ⊗ A).left.Opens :=
  μ[A].left ⁻¹ᵁ V t.1 ⊓ (fst A A).left ⁻¹ᵁ V t.2.1 ⊓ (snd A A).left ⁻¹ᵁ V t.2.2

theorem pairOpen_le_mul (V : J → A.left.Opens) (t t' : J × J × J) :
    pairOpen V t ⊓ pairOpen V t' ≤ μ[A].left ⁻¹ᵁ (V t.1 ⊓ V t'.1) :=
  fun _ h ↦ ⟨h.1.1.1, h.2.1.1⟩

theorem pairOpen_le_fst (V : J → A.left.Opens) (t t' : J × J × J) :
    pairOpen V t ⊓ pairOpen V t' ≤ (fst A A).left ⁻¹ᵁ (V t.2.1 ⊓ V t'.2.1) :=
  fun _ h ↦ ⟨h.1.1.2, h.2.1.2⟩

theorem pairOpen_le_snd (V : J → A.left.Opens) (t t' : J × J × J) :
    pairOpen V t ⊓ pairOpen V t' ≤ (snd A A).left ⁻¹ᵁ (V t.2.2 ⊓ V t'.2.2) :=
  fun _ h ↦ ⟨h.1.2, h.2.2⟩

theorem iSup_pairOpen (V : J → A.left.Opens) (hV : ⨆ a, V a = ⊤) : ⨆ t, pairOpen V t = ⊤ := by
  have hm : ∀ y : A.left, ∃ a, y ∈ V a := fun y ↦
    TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ a, V a by rw [hV]; trivial)
  refine eq_top_iff.2 fun z _ ↦ TopologicalSpace.Opens.mem_iSup.2 ?_
  obtain ⟨a, ha⟩ := hm (μ[A].left z)
  obtain ⟨b, hb⟩ := hm ((fst A A).left z)
  obtain ⟨c, hc⟩ := hm ((snd A A).left z)
  exact ⟨(a, b, c), ⟨⟨ha, hb⟩, hc⟩⟩

def pairCocycle (V : J → A.left.Opens) (φ : ∀ a b, Γ(A.left, V a ⊓ V b)) (t t' : J × J × J) :
    Γ((A ⊗ A).left, pairOpen V t ⊓ pairOpen V t') :=
  (μ[A].left.appLE _ _ (pairOpen_le_mul V t t')).hom (φ t.1 t'.1) -
    ((fst A A).left.appLE _ _ (pairOpen_le_fst V t t')).hom (φ t.2.1 t'.2.1) -
    ((snd A A).left.appLE _ _ (pairOpen_le_snd V t t')).hom (φ t.2.2 t'.2.2)

abbrev transSrc (P : GPt A) : Over (Sp K) :=
  Over.mk (spMap ((algebraMap P.B (DualNumber P.B)).comp (algebraMap K P.B)))

def transFst (P : GPt A) : transSrc P ⟶ A :=
  Over.homMk (spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x) (by
    have hx : P.x ≫ A.hom = spMap (algebraMap K P.B) :=
      (congrArg (P.x ≫ ·) (Category.comp_id _)).symm.trans P.w
    change (spMap _ ≫ P.x) ≫ A.hom = spMap _
    rw [Category.assoc, hx, ← Cris.spMap_comp])

def transSnd (P : GPt A) (v : epsR K ⟶ A) : transSrc P ⟶ A :=
  Over.homMk (spMap (dualMap (algebraMap K P.B)) ≫ v.left) (by
    change (spMap _ ≫ v.left) ≫ A.hom = spMap _
    rw [Category.assoc, Over.w v]
    change spMap _ ≫ spMap _ = spMap _
    rw [← Cris.spMap_comp, dualMap_comp_algebraMap])

def transPair (P : GPt A) (v : epsR K ⟶ A) : Sp (DualNumber P.B) ⟶ (A ⊗ A).left :=
  (lift (transFst P) (transSnd P v)).left

theorem transPair_isTransl (P : GPt A) (v : epsR K ⟶ A) :
    IsTransl (algebraMap K P.B) P.x v (transPair P v ≫ μ[A].left) :=
  ⟨_, _, rfl, rfl, by rw [transPair, ← Over.comp_left]; rfl⟩

theorem transPair_mul (P : GPt A) (v : epsR K ⟶ A) : transPair P v ≫ μ[A].left = P.trx v :=
  (transPair_isTransl P v).unique (P.isTransl_trx v)

theorem transPair_fst (P : GPt A) (v : epsR K ⟶ A) :
    transPair P v ≫ (fst A A).left = spMap (algebraMap P.B (DualNumber P.B)) ≫ P.x := by
  rw [transPair, ← Over.comp_left, lift_fst]; rfl

theorem transPair_snd (P : GPt A) (v : epsR K ⟶ A) :
    transPair P v ≫ (snd A A).left = spMap (dualMap (algebraMap K P.B)) ≫ v.left := by
  rw [transPair, ← Over.comp_left, lift_snd]; rfl

theorem transPair_map {P Q : GPt A} (φ : P.Hom Q) (v : epsR K ⟶ A) :
    spMap (dualMap (φ.ρ : P.B →+* Q.B)) ≫ transPair P v = transPair Q v := by
  let j : transSrc Q ⟶ transSrc P := Over.homMk (spMap (dualMap (φ.ρ : P.B →+* Q.B))) (by
    change spMap _ ≫ spMap _ = spMap _
    rw [← Cris.spMap_comp, ← RingHom.comp_assoc, dualMap_comp_algebraMap, RingHom.comp_assoc,
      φ.ρ.comp_algebraMap])
  have h1 : j ≫ transFst P = transFst Q := by
    apply Over.OverMorphism.ext
    change spMap _ ≫ spMap _ ≫ P.x = spMap _ ≫ Q.x
    rw [← φ.pt, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp,
      dualMap_comp_algebraMap]
  have h2 : j ≫ transSnd P v = transSnd Q v := by
    apply Over.OverMorphism.ext
    change spMap _ ≫ spMap _ ≫ v.left = spMap _ ≫ v.left
    rw [← Category.assoc, ← Cris.spMap_comp, dualMap_comp_dualMap, φ.ρ.comp_algebraMap]
  have h3 : j ≫ lift (transFst P) (transSnd P v) = lift (transFst Q) (transSnd Q v) := by
    rw [comp_lift, h1, h2]
  exact congrArg Over.Hom.left h3

theorem tangent_in {v : epsR K ⟶ A} (hv : IsTangent v) {U : A.left.Opens} (h : ⊤ ≤ η[A].left ⁻¹ᵁ U) :
    ⊤ ≤ v.left ⁻¹ᵁ U := by
  intro p _
  have hs : Function.Surjective (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) := by
    intro q
    refine ⟨spMap (algebraMap K (DualNumber K)) q, ?_⟩
    refine PrimeSpectrum.ext (Ideal.ext fun c ↦ ?_)
    change algebraMap K (DualNumber K) c.fst ∈ q.asIdeal ↔ c ∈ q.asIdeal
    have hn : c - algebraMap K (DualNumber K) c.fst ∈ q.asIdeal := by
      refine q.isPrime.mem_of_pow_mem 2 ?_
      have : (c - algebraMap K (DualNumber K) c.fst) ^ 2 = 0 := by
        ext <;> simp [pow_two, TrivSqZeroExt.algebraMap_eq_inl]
      rw [this]; exact zero_mem _
    exact ⟨fun hc ↦ by simpa using add_mem hn hc, fun hc ↦ by simpa using sub_mem hc hn⟩
  obtain ⟨q, rfl⟩ := hs p
  have := h (Set.mem_univ q)
  rw [← hv] at this
  exact this

theorem transPair_in (V : J → A.left.Opens) (P : GPt A) {v : epsR K ⟶ A} (hv : IsTangent v) {a c : J}
    (ha : P.In (V a)) (hc : ⊤ ≤ v.left ⁻¹ᵁ V c) : ⊤ ≤ transPair P v ⁻¹ᵁ pairOpen V (a, a, c) := by
  intro p _
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have := (ha.tr hv) (Set.mem_univ p)
    change p ∈ (P.trx v) ⁻¹ᵁ V a at this
    rw [← transPair_mul] at this
    exact this
  · have := ha (Set.mem_univ ((spMap (algebraMap P.B (DualNumber P.B))).base p))
    change p ∈ (transPair P v ≫ (fst A A).left) ⁻¹ᵁ V a
    rw [transPair_fst]
    exact this
  · change p ∈ (transPair P v ≫ (snd A A).left) ⁻¹ᵁ V c
    rw [transPair_snd]
    exact hc (Set.mem_univ _)

@[reducible] def tanPt (P : GPt A) (v : epsR K ⟶ A) : GPt A where
  B := DualNumber P.B
  x := spMap (dualMap (algebraMap K P.B)) ≫ v.left
  w := (congrArg ((spMap (dualMap (algebraMap K P.B)) ≫ v.left) ≫ ·) (Category.comp_id A.hom)).trans
    (Over.w (transSnd P v))

theorem valR_sub {C : Type} [CommRing C] {X : Scheme.{0}} (x : Sp C ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f g : Γ(X, U)) : valR x U (f - g) = valR x U f - valR x U g := by
  simp only [GlobalTheory.Points.valR_eq x U h, map_sub]

end GlobalTheory.CechInv

namespace GlobalTheory.CechInv

theorem ext_of_valR {X : Scheme.{0}} (U : X.Opens) (f g : Γ(X, U))
    (H : ∀ (C : Type) [CommRing C] (x : Sp C ⟶ X), ⊤ ≤ x ⁻¹ᵁ U → valR x U f = valR x U g) : f = g := by
  refine X.IsSheaf.section_ext (U := Opposite.op U) fun p hp ↦ ?_
  obtain ⟨W, hW, hpW, hWU⟩ := exists_isAffineOpen_mem_and_subset hp
  refine ⟨W, hWU, hpW, ?_⟩
  have h := GlobalTheory.Points.le_preimage_specMap_fromSpec (C := Γ(X, W)) hW (𝟙 _)
  have e := H Γ(X, W) _ (GlobalTheory.Points.le_preimage_mono _ hWU h)
  rw [← GlobalTheory.Points.valR_res _ hWU h, ← GlobalTheory.Points.valR_res _ hWU h, GlobalTheory.Points.valR_eq _ _ h,
    GlobalTheory.Points.valR_eq _ _ h, GlobalTheory.Points.valMap_specMap_fromSpec] at e
  exact e

variable {K : Type} [Field K] {A : Over (Sp K)} {J : Type}

theorem cocycle_at {V : J → A.left.Opens} {φ : ∀ a b, Γ(A.left, V a ⊓ V b)}
    (hφ : ∀ (a b c : J) (P : GPt A), P.In (V a) → P.In (V b) → P.In (V c) →
      valR P.x _ (φ a b) + valR P.x _ (φ b c) = valR P.x _ (φ a c))
    {C : Type} [CommRing C] (x : Sp C ⟶ A.left) {a b c : J} (ha : ⊤ ≤ x ⁻¹ᵁ V a) (hb : ⊤ ≤ x ⁻¹ᵁ V b)
    (hc : ⊤ ≤ x ⁻¹ᵁ V c) : valR x _ (φ a b) + valR x _ (φ b c) = valR x _ (φ a c) := by
  letI : Algebra K C := (Spec.preimage (x ≫ A.hom)).hom.toAlgebra
  exact hφ a b c ⟨C, x, (congrArg (x ≫ ·) (Category.comp_id _)).trans (Spec.map_preimage _).symm⟩ ha hb hc

variable [GrpObj A]

theorem valR_pairCocycle (V : J → A.left.Opens) (φ : ∀ a b, Γ(A.left, V a ⊓ V b)) (t t' : J × J × J)
    {C : Type} [CommRing C] (z : Sp C ⟶ (A ⊗ A).left) (hz : ⊤ ≤ z ⁻¹ᵁ (pairOpen V t ⊓ pairOpen V t')) :
    valR z _ (pairCocycle V φ t t') = valR (z ≫ μ[A].left) _ (φ t.1 t'.1) -
      valR (z ≫ (fst A A).left) _ (φ t.2.1 t'.2.1) - valR (z ≫ (snd A A).left) _ (φ t.2.2 t'.2.2) := by
  rw [pairCocycle, valR_sub _ _ hz, valR_sub _ _ hz, GlobalTheory.Points.valR_appLE _ _ _ hz,
    GlobalTheory.Points.valR_appLE _ _ _ hz, GlobalTheory.Points.valR_appLE _ _ _ hz]

theorem pairCocycle_cocycle (V : J → A.left.Opens) (φ : ∀ a b, Γ(A.left, V a ⊓ V b))
    (hφ : ∀ (a b c : J) (P : GPt A), P.In (V a) → P.In (V b) → P.In (V c) →
      valR P.x _ (φ a b) + valR P.x _ (φ b c) = valR P.x _ (φ a c)) (a b d : J × J × J) :
    ((A ⊗ A).left.presheaf.map (homOfLE (inf_le_left : pairOpen V a ⊓ pairOpen V b ⊓ pairOpen V d ≤ pairOpen V a ⊓ pairOpen V b)).op).hom (pairCocycle V φ a b) + ((A ⊗ A).left.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right : pairOpen V a ⊓ pairOpen V b ⊓ pairOpen V d ≤ pairOpen V b ⊓ pairOpen V d)).op).hom (pairCocycle V φ b d) = ((A ⊗ A).left.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right : pairOpen V a ⊓ pairOpen V b ⊓ pairOpen V d ≤ pairOpen V a ⊓ pairOpen V d)).op).hom (pairCocycle V φ a d) := by
  refine ext_of_valR _ _ _ fun C _ z hz ↦ ?_
  have ha : ⊤ ≤ z ⁻¹ᵁ pairOpen V a := fun _ h ↦ (hz h).1.1
  have hb : ⊤ ≤ z ⁻¹ᵁ pairOpen V b := fun _ h ↦ (hz h).1.2
  have hd : ⊤ ≤ z ⁻¹ᵁ pairOpen V d := fun _ h ↦ (hz h).2
  rw [GlobalTheory.Points.valR_add _ _ hz, GlobalTheory.Points.valR_res _ _ hz, GlobalTheory.Points.valR_res _ _ hz,
    GlobalTheory.Points.valR_res _ _ hz, valR_pairCocycle V φ a b z (fun _ h ↦ ⟨ha h, hb h⟩),
    valR_pairCocycle V φ b d z (fun _ h ↦ ⟨hb h, hd h⟩), valR_pairCocycle V φ a d z (fun _ h ↦ ⟨ha h, hd h⟩)]
  have e1 := cocycle_at hφ (z ≫ μ[A].left) (a := a.1) (b := b.1) (c := d.1)
    (fun _ h ↦ (ha h).1.1) (fun _ h ↦ (hb h).1.1) (fun _ h ↦ (hd h).1.1)
  have e2 := cocycle_at hφ (z ≫ (fst A A).left) (a := a.2.1) (b := b.2.1) (c := d.2.1)
    (fun _ h ↦ (ha h).1.2) (fun _ h ↦ (hb h).1.2) (fun _ h ↦ (hd h).1.2)
  have e3 := cocycle_at hφ (z ≫ (snd A A).left) (a := a.2.2) (b := b.2.2) (c := d.2.2)
    (fun _ h ↦ (ha h).2) (fun _ h ↦ (hb h).2) (fun _ h ↦ (hd h).2)
  linear_combination e1 - e2 - e3

omit [GrpObj A] in

theorem axis_coboundary {I : Type} (V : J → A.left.Opens) (φ : ∀ a b, Γ(A.left, V a ⊓ V b))
    (hφ : ∀ (a b c : J) (P : GPt A), P.In (V a) → P.In (V b) → P.In (V c) →
      valR P.x _ (φ a b) + valR P.x _ (φ b c) = valR P.x _ (φ a c))
    (e : A.left ⟶ A.left) (c₀ : J) (he : ⊤ ≤ e ⁻¹ᵁ V c₀) (W : I → A.left.Opens) (p q r : I → J)
    (hp : ∀ t, W t ≤ V (p t)) (hq : ∀ t, W t ≤ V (q t)) (hr : ∀ t, W t ≤ e ⁻¹ᵁ V (r t)) :
    ∃ ψ : ∀ t, Γ(A.left, W t), ∀ (t t' : I) (C : Type) [CommRing C] (x : Sp C ⟶ A.left), ⊤ ≤ x ⁻¹ᵁ W t →
      ⊤ ≤ x ⁻¹ᵁ W t' → valR x _ (φ (p t) (p t')) - valR x _ (φ (q t) (q t')) - valR (x ≫ e) _ (φ (r t) (r t')) =
        valR x _ (ψ t) - valR x _ (ψ t') := by
  have h1 : ∀ t, W t ≤ V (p t) ⊓ V (q t) := fun t ↦ le_inf (hp t) (hq t)
  have h2 : ∀ t, W t ≤ e ⁻¹ᵁ (V (r t) ⊓ V c₀) := fun t _ h ↦ ⟨hr t h, he trivial⟩
  refine ⟨fun t ↦ (A.left.presheaf.map (homOfLE (h1 t)).op).hom (φ (p t) (q t)) -
    (e.appLE _ _ (h2 t)).hom (φ (r t) c₀), fun t t' C _ x ht ht' ↦ ?_⟩
  rw [valR_sub _ _ ht, valR_sub _ _ ht', GlobalTheory.Points.valR_res _ _ ht, GlobalTheory.Points.valR_res _ _ ht',
    GlobalTheory.Points.valR_appLE _ _ _ ht, GlobalTheory.Points.valR_appLE _ _ _ ht']
  have e1 := cocycle_at hφ x (GlobalTheory.Points.le_preimage_mono x (hp t) ht)
    (GlobalTheory.Points.le_preimage_mono x (hp t') ht') (GlobalTheory.Points.le_preimage_mono x (hq t') ht')
  have e2 := cocycle_at hφ x (GlobalTheory.Points.le_preimage_mono x (hp t) ht)
    (GlobalTheory.Points.le_preimage_mono x (hq t) ht) (GlobalTheory.Points.le_preimage_mono x (hq t') ht')
  have e3 := cocycle_at hφ (x ≫ e) (GlobalTheory.Points.le_preimage_comp x e (hr t) ht)
    (GlobalTheory.Points.le_preimage_comp x e (hr t') ht') (GlobalTheory.Points.le_preimage_comp x e he (GlobalTheory.Points.le_preimage_top x))
  linear_combination e1 - e2 - e3

theorem exists_one_in (V : J → A.left.Opens) (hV : ⨆ a, V a = ⊤) : ∃ c, ⊤ ≤ η[A].left ⁻¹ᵁ V c :=
  GlobalTheory.Points.exists_le_preimage_of_iSup_eq_top (C := K) η[A].left hV

theorem pairCocycle_left (V : J → A.left.Opens) (φ : ∀ a b, Γ(A.left, V a ⊓ V b))
    (hφ : ∀ (a b c : J) (P : GPt A), P.In (V a) → P.In (V b) → P.In (V c) →
      valR P.x _ (φ a b) + valR P.x _ (φ b c) = valR P.x _ (φ a c))
    (e : A.left ⟶ A.left) (c₀ : J) (he : ⊤ ≤ e ⁻¹ᵁ V c₀) (i : A.left ⟶ (A ⊗ A).left)
    (i1 : i ≫ μ[A].left = 𝟙 _) (i2 : i ≫ (fst A A).left = 𝟙 _) (i3 : i ≫ (snd A A).left = e) :
    ∃ ψ : ∀ t : J × J × J, Γ(A.left, i ⁻¹ᵁ pairOpen V t), ∀ t t',
      (i.app (pairOpen V t ⊓ pairOpen V t')).hom (pairCocycle V φ t t') =
        (A.left.presheaf.map (homOfLE (show i ⁻¹ᵁ (pairOpen V t ⊓ pairOpen V t') ≤ i ⁻¹ᵁ pairOpen V t from
          fun _ h => h.1)).op).hom (ψ t) -
        (A.left.presheaf.map (homOfLE (show i ⁻¹ᵁ (pairOpen V t ⊓ pairOpen V t') ≤ i ⁻¹ᵁ pairOpen V t' from
          fun _ h => h.2)).op).hom (ψ t') := by
  have k1 : ∀ t, i ⁻¹ᵁ pairOpen V t ≤ V t.1 := fun t y h ↦ by
    have : y ∈ (i ≫ μ[A].left) ⁻¹ᵁ V t.1 := h.1.1
    rwa [i1] at this
  have k2 : ∀ t, i ⁻¹ᵁ pairOpen V t ≤ V t.2.1 := fun t y h ↦ by
    have : y ∈ (i ≫ (fst A A).left) ⁻¹ᵁ V t.2.1 := h.1.2
    rwa [i2] at this
  have k3 : ∀ t, i ⁻¹ᵁ pairOpen V t ≤ e ⁻¹ᵁ V t.2.2 := fun t y h ↦ by
    have : y ∈ (i ≫ (snd A A).left) ⁻¹ᵁ V t.2.2 := h.2
    rwa [i3] at this
  obtain ⟨ψ, hψ⟩ := axis_coboundary V φ hφ e c₀ he (fun t ↦ i ⁻¹ᵁ pairOpen V t) (fun t ↦ t.1)
    (fun t ↦ t.2.1) (fun t ↦ t.2.2) k1 k2 k3
  refine ⟨ψ, fun t t' ↦ ext_of_valR _ _ _ fun C _ x hx ↦ ?_⟩
  have hx' : ⊤ ≤ (x ≫ i) ⁻¹ᵁ (pairOpen V t ⊓ pairOpen V t') := GlobalTheory.Points.le_preimage_comp x i le_rfl hx
  rw [← GlobalTheory.Points.valR_comp x i, valR_pairCocycle V φ t t' (x ≫ i) hx', valR_sub _ _ hx, GlobalTheory.Points.valR_res _ _ hx,
    GlobalTheory.Points.valR_res _ _ hx, Category.assoc, Category.assoc, Category.assoc, i1, i2, i3, Category.comp_id]
  exact hψ t t' C x (fun _ h ↦ (hx h).1) (fun _ h ↦ (hx h).2)

theorem pairCocycle_right (V : J → A.left.Opens) (φ : ∀ a b, Γ(A.left, V a ⊓ V b))
    (hφ : ∀ (a b c : J) (P : GPt A), P.In (V a) → P.In (V b) → P.In (V c) →
      valR P.x _ (φ a b) + valR P.x _ (φ b c) = valR P.x _ (φ a c))
    (e : A.left ⟶ A.left) (c₀ : J) (he : ⊤ ≤ e ⁻¹ᵁ V c₀) (i : A.left ⟶ (A ⊗ A).left)
    (i1 : i ≫ μ[A].left = 𝟙 _) (i2 : i ≫ (fst A A).left = e) (i3 : i ≫ (snd A A).left = 𝟙 _) :
    ∃ ψ : ∀ t : J × J × J, Γ(A.left, i ⁻¹ᵁ pairOpen V t), ∀ t t',
      (i.app (pairOpen V t ⊓ pairOpen V t')).hom (pairCocycle V φ t t') =
        (A.left.presheaf.map (homOfLE (show i ⁻¹ᵁ (pairOpen V t ⊓ pairOpen V t') ≤ i ⁻¹ᵁ pairOpen V t from
          fun _ h => h.1)).op).hom (ψ t) -
        (A.left.presheaf.map (homOfLE (show i ⁻¹ᵁ (pairOpen V t ⊓ pairOpen V t') ≤ i ⁻¹ᵁ pairOpen V t' from
          fun _ h => h.2)).op).hom (ψ t') := by
  have k1 : ∀ t, i ⁻¹ᵁ pairOpen V t ≤ V t.1 := fun t y h ↦ by
    have : y ∈ (i ≫ μ[A].left) ⁻¹ᵁ V t.1 := h.1.1
    rwa [i1] at this
  have k2 : ∀ t, i ⁻¹ᵁ pairOpen V t ≤ e ⁻¹ᵁ V t.2.1 := fun t y h ↦ by
    have : y ∈ (i ≫ (fst A A).left) ⁻¹ᵁ V t.2.1 := h.1.2
    rwa [i2] at this
  have k3 : ∀ t, i ⁻¹ᵁ pairOpen V t ≤ V t.2.2 := fun t y h ↦ by
    have : y ∈ (i ≫ (snd A A).left) ⁻¹ᵁ V t.2.2 := h.2
    rwa [i3] at this
  obtain ⟨ψ, hψ⟩ := axis_coboundary V φ hφ e c₀ he (fun t ↦ i ⁻¹ᵁ pairOpen V t) (fun t ↦ t.1)
    (fun t ↦ t.2.2) (fun t ↦ t.2.1) k1 k3 k2
  refine ⟨ψ, fun t t' ↦ ext_of_valR _ _ _ fun C _ x hx ↦ ?_⟩
  have hx' : ⊤ ≤ (x ≫ i) ⁻¹ᵁ (pairOpen V t ⊓ pairOpen V t') := GlobalTheory.Points.le_preimage_comp x i le_rfl hx
  rw [← GlobalTheory.Points.valR_comp x i, valR_pairCocycle V φ t t' (x ≫ i) hx', valR_sub _ _ hx, GlobalTheory.Points.valR_res _ _ hx,
    GlobalTheory.Points.valR_res _ _ hx, Category.assoc, Category.assoc, Category.assoc, i1, i2, i3, Category.comp_id,
    sub_right_comm]
  exact hψ t t' C x (fun _ h ↦ (hx h).1) (fun _ h ↦ (hx h).2)

theorem const_in {U : A.left.Opens} (h : ⊤ ≤ η[A].left ⁻¹ᵁ U) : ⊤ ≤ (toUnit A ≫ η[A]).left ⁻¹ᵁ U := by
  rw [Over.comp_left, Scheme.Hom.comp_preimage]
  exact fun _ _ ↦ h trivial

end GlobalTheory.CechInv

namespace GlobalTheory.CechInv

theorem deriv_cocycle_isCoboundary : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (J : Type) (V : J → A.left.Opens), ⨆ a, V a = ⊤ → ∀ φ : ∀ a b, Γ(A.left, V a ⊓ V b), (∀ (a b c : J) (P : GPt A), P.In (V a) → P.In (V b) → P.In (V c) → valR P.x _ (φ a b) + valR P.x _ (φ b c) = valR P.x _ (φ a c)) → ∀ v : epsR K ⟶ A, IsTangent v → ∃ ψ : J → PtFn (A.hom ≫ 𝟙 (Sp K)), (∀ a, IsNat (V a) (ψ a)) ∧ ∀ (a b : J) (P : GPt A), P.In (V a) → P.In (V b) → (valR (P.trx v) _ (φ a b)).snd = ψ a P - ψ b P := by
  intro K _ A _ hA J V hV φ hφ v hv
  obtain ⟨c₀, hc₀⟩ : ∃ c, ⊤ ≤ η[A].left ⁻¹ᵁ V c := by
    obtain ⟨p⟩ : Nonempty (Sp K) := inferInstance
    obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.1 (show η[A].left p ∈ ⨆ a, V a by rw [hV]; trivial)
    exact ⟨c, fun q _ ↦ by
      have e : q = p := Subsingleton.elim (α := ↥(Sp K)) q p
      rw [e]; exact hc⟩
  have hvc : ⊤ ≤ v.left ⁻¹ᵁ V c₀ := tangent_in hv hc₀
  haveI := hA.proper
  have hsep : IsSeparated A.hom := inferInstance
  have hqc : QuasiCompact A.hom := inferInstance
  obtain ⟨Ψ, hΨ⟩ := GlobalTheory.KuennethOne.kuenneth_injective K A A η[A] η[A] hsep hqc hsep hqc
    (GlobalTheory.globalFns_holds _ A hA) (GlobalTheory.globalFns_holds _ A hA) (J × J × J) (pairOpen V) (iSup_pairOpen V hV)
    (pairCocycle V φ) (pairCocycle_cocycle V φ hφ)
    (pairCocycle_left V φ hφ _ c₀ (const_in hc₀) (lift (𝟙 A) (toUnit A ≫ η[A])).left
      (by rw [← Over.comp_left, MonObj.lift_comp_one_right]; rfl) (by rw [← Over.comp_left, lift_fst]; rfl)
      (by rw [← Over.comp_left, lift_snd]))
    (pairCocycle_right V φ hφ _ c₀ (const_in hc₀) (lift (toUnit A ≫ η[A]) (𝟙 A)).left
      (by rw [← Over.comp_left, MonObj.lift_comp_one_left]; rfl) (by rw [← Over.comp_left, lift_fst])
      (by rw [← Over.comp_left, lift_snd]; rfl))
  refine ⟨fun a P ↦ (valR (transPair P v) (pairOpen V (a, a, c₀)) (Ψ (a, a, c₀))).snd, fun a P Q f hP ↦ ?_,
    fun a b P ha hb ↦ ?_⟩
  · change (valR (transPair Q v) _ _).snd = f.ρ (valR (transPair P v) _ _).snd
    rw [← transPair_map f v, GlobalTheory.Points.valR_spMap_comp _ _ _ (transPair_in V P hv hP hvc)]
    simp [dualMap]
  · have hz := transPair_in V P hv ha hvc
    have hz' := transPair_in V P hv hb hvc
    have hzz : ⊤ ≤ transPair P v ⁻¹ᵁ (pairOpen V (a, a, c₀) ⊓ pairOpen V (b, b, c₀)) :=
      fun p hp ↦ ⟨hz hp, hz' hp⟩
    have e := congrArg (valR (transPair P v) _) (hΨ (a, a, c₀) (b, b, c₀))
    rw [valR_sub _ _ hzz, GlobalTheory.Points.valR_res _ _ hzz, GlobalTheory.Points.valR_res _ _ hzz, pairCocycle,
      valR_sub _ _ hzz, valR_sub _ _ hzz, GlobalTheory.Points.valR_appLE _ _ _ hzz, GlobalTheory.Points.valR_appLE _ _ _ hzz,
      GlobalTheory.Points.valR_appLE _ _ _ hzz, transPair_mul, transPair_fst, transPair_snd,
      GlobalTheory.Points.valR_spMap_comp _ _ _ (ha.inf hb)] at e
    have hv' : (tanPt P v).In (V c₀) := fun p _ ↦ hvc (Set.mem_univ _)
    have h0 := hφ c₀ c₀ c₀ (tanPt P v) hv' hv' hv'
    have h0' : valR (spMap (dualMap (algebraMap K P.B)) ≫ v.left) (V c₀ ⊓ V c₀) (φ c₀ c₀) = 0 := by
      have : ∀ x : DualNumber P.B, x + x = x → x = 0 := fun x hx ↦ by linear_combination hx
      exact this _ h0
    rw [h0'] at e
    have := congrArg TrivSqZeroExt.snd e
    simpa [TrivSqZeroExt.algebraMap_eq_inl] using this

end GlobalTheory.CechInv
