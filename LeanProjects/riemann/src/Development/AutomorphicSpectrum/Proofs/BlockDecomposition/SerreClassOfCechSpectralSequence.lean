import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

universe w v u

namespace GlobalTheory.CompanionTheory.CechSerre

section Abstract

variable {R : Type} [CommRing R]

def colMap (K : DCx.{w} R) (p : ℕ) : Cx.Hom (K.col p) (K.col (p + 1)) (RingHom.id R) :=
  ⟨fun q => K.dh p q, fun q x => (K.hv p q x).symm⟩

def colH (K : DCx.{w} R) (q : ℕ) : Cx.{w} R where
  X p := (K.col p).H q
  d p := (colMap K p).mapH q
  dd p x := by
    obtain ⟨a, ha, rfl⟩ := (P.cls_surj (K.col p) q).1 x
    have h1 : (K.col (p + 1)).d q ((colMap K p).f q a) = 0 := by
      rw [(colMap K p).comm, ha, map_zero]
    have h2 : (K.col (p + 2)).d q ((colMap K (p + 1)).f q ((colMap K p).f q a)) = 0 := by
      rw [(colMap K (p + 1)).comm, h1, map_zero]
    rw [P.mapH_cls _ q a ha h1, P.mapH_cls _ q _ h1 h2, (P.cls_surj (K.col (p + 2)) q).2.1]
    have h3 : (colMap K (p + 1)).f q ((colMap K p).f q a) = 0 := K.hh p q a
    rw [h3]
    exact Submodule.zero_mem _

end Abstract

section Nerve

variable {C : Type u} [Category.{v} C] {ι : Type}

def idxF (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) : C ⥤ Type where
  obj T := {α // U α T}
  map φ := TypeCat.ofHom fun a => ⟨a.1, hU a.1 φ a.2⟩

def idxπ (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) : idxF U hU ⟶ (Functor.const C).obj PUnit where
  app T := TypeCat.ofHom fun _ => PUnit.unit

def tupF (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) {p : ℕ} (i : Fin (p + 1) → ι) :
    (capT U i).FullSubcategory ⥤ (CH.cech (idxπ U hU) p).Elements where
  obj T := ⟨T.obj, ⟨fun k => ⟨i k, T.property k⟩, fun _ _ => rfl⟩⟩
  map φ := ⟨φ.hom, Subtype.ext (funext fun k => Subtype.ext rfl)⟩

variable {R : Type} [CommRing R]

def tupM (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (F : C ⥤ ModuleCat.{w} R) {p : ℕ} (i : Fin (p + 1) → ι) :
    CH.Mor (CH.elF (CH.cech (idxπ U hU) p) F) ((capT U i).ι ⋙ F) (RingHom.id R) where
  G := tupF U hU i
  τ _ := LinearMap.id
  nat _ _ := rfl

abbrev dbl (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (F : C ⥤ ModuleCat.{w} R) : DCx.{max u v w} R :=
  (CH.cechCos (idxπ U hU) F).dcx

end Nerve

section Serre

variable {R : Type} [CommRing R] (𝒮 : Serre.{w} R)

theorem serre_of_injective {M N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Injective f) (hN : 𝒮.P N) : 𝒮.P M := by
  refine 𝒮.mid PUnit.{w + 1} M N 0 f ?_ (𝒮.zero _ inferInstance) hN
  intro x
  constructor
  · intro hx
    exact ⟨0, hf (by simpa using hx.symm) ⟩
  · rintro ⟨y, rfl⟩
    simp

theorem serre_of_surjective {M N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) (hM : 𝒮.P M) : 𝒮.P N := by
  refine 𝒮.mid M N PUnit.{w + 1} f 0 ?_ hM (𝒮.zero _ inferInstance)
  intro x
  constructor
  · intro _
    exact hf x
  · rintro _
    rfl

theorem serre_of_equiv {M N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (hM : 𝒮.P M) : 𝒮.P N :=
  serre_of_surjective 𝒮 e.toLinearMap e.surjective hM

theorem serre_step {Z H E : Type w} [AddCommGroup Z] [Module R Z] [AddCommGroup H] [Module R H] [AddCommGroup E] [Module R E]
    (c : Z →ₗ[R] H) (ψ : Z →ₗ[R] E) (B : Submodule R H) (hk : ∀ z, ψ z = 0 → c z ∈ B)
    (hB : 𝒮.P B) (hE : 𝒮.P E) : 𝒮.P (LinearMap.range c) := by
  set B' : Submodule R (LinearMap.range c) := B.comap (LinearMap.range c).subtype with hB'
  have h1 : 𝒮.P B' := by
    refine serre_of_injective 𝒮 (f := (((LinearMap.range c).subtype.comp B'.subtype).codRestrict B fun x => x.2)) ?_ hB
    intro x y h
    have h' : ((x.1 : LinearMap.range c) : H) = y.1 := congrArg (fun t : B => (t : H)) h
    exact Subtype.ext (Subtype.ext h')
  have h2 : 𝒮.P (Z ⧸ LinearMap.ker ψ) :=
    serre_of_injective 𝒮 ((LinearMap.ker ψ).liftQ ψ le_rfl)
      (LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)) hE
  have h3 : 𝒮.P (LinearMap.range c ⧸ B') := by
    refine serre_of_surjective 𝒮 ((LinearMap.ker ψ).liftQ (B'.mkQ.comp c.rangeRestrict) ?_) ?_ h2
    · intro z hz
      simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hk z hz
    · intro x
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
      obtain ⟨z, hz⟩ := c.surjective_rangeRestrict y
      exact ⟨Submodule.Quotient.mk z, by simp [hz]⟩
  refine 𝒮.mid B' _ _ B'.subtype B'.mkQ ?_ h1 h3
  exact LinearMap.exact_subtype_mkQ B'

end Serre

section Filt

variable {R : Type} [CommRing R] (K : DCx.{w} R) (n : ℕ)

def Zf (a : ℕ) : Submodule R (K.tot.Z n) where
  carrier := {z | ∀ p q, p < a → z.1.1 p q = 0}
  add_mem' {x y} hx hy p q h := by
    change x.1.1 p q + y.1.1 p q = 0
    rw [hx p q h, hy p q h, add_zero]
  zero_mem' p q h := rfl
  smul_mem' c x hx p q h := by
    change c • x.1.1 p q = 0
    rw [hx p q h, smul_zero]

def clsZ (a : ℕ) : Zf K n a →ₗ[R] K.tot.H n :=
  (Submodule.mkQ _).comp (Zf K n a).subtype

def Ff (a : ℕ) : Submodule R (K.tot.H n) := LinearMap.range (clsZ K n a)

end Filt

section Pieces

theorem pi_H_bij : ∀ {R : Type} [CommRing R] {A : Cx.{w} R} {I : Type} (B : I → Cx.{w} R) (φ : ∀ i, Cx.Hom A (B i) (RingHom.id R)), (∀ q, Function.Bijective (fun (x : A.X q) i => (φ i).f q x)) → ∀ q, Function.Bijective (fun (x : A.H q) i => (φ i).mapH q x) := by
  intro R _ A I B φ hb q
  constructor
  · intro x y hxy
    obtain ⟨a, ha, rfl⟩ := (P.cls_surj A q).1 x
    obtain ⟨b, hb', rfl⟩ := (P.cls_surj A q).1 y
    have hz : ∀ i, (B i).d q ((φ i).f q a) = 0 := fun i => by rw [(φ i).comm, ha, map_zero]
    have hz' : ∀ i, (B i).d q ((φ i).f q b) = 0 := fun i => by rw [(φ i).comm, hb', map_zero]
    have hi : ∀ i, (φ i).f q a - (φ i).f q b ∈ (B i).B q := by
      intro i
      have := congrFun hxy i
      simp only at this
      rw [P.mapH_cls _ q a ha (hz i), P.mapH_cls _ q b hb' (hz' i)] at this
      exact ((P.cls_surj (B i) q).2.2.1 _ _ _ _).1 this
    refine ((P.cls_surj A q).2.2.1 _ _ _ _).2 ?_
    cases q with
    | zero =>
      show _ ∈ (⊥ : Submodule R _)
      rw [Submodule.mem_bot, sub_eq_zero]
      refine (hb 0).1 (funext fun i => ?_)
      exact sub_eq_zero.1 ((Submodule.mem_bot R).1 (hi i))
    | succ q =>
      choose w hw using hi
      obtain ⟨w', hw'⟩ := (hb q).2 w
      refine ⟨w', ?_⟩
      refine (hb (q + 1)).1 (funext fun i => ?_)
      simp only
      rw [← (φ i).comm, map_sub, show (φ i).f q w' = w i from congrFun hw' i, hw i]
  · intro y
    choose a ha hy using fun i => (P.cls_surj (B i) q).1 (y i)
    obtain ⟨z, hz⟩ := (hb q).2 a
    have hzi : ∀ i, (φ i).f q z = a i := fun i => congrFun hz i
    have hdz : A.d q z = 0 := by
      refine (hb (q + 1)).1 (funext fun i => ?_)
      simp only
      rw [← (φ i).comm, hzi, ha, map_zero]
    refine ⟨A.cls z hdz, funext fun i => ?_⟩
    have h2 : (B i).d q ((φ i).f q z) = 0 := by rw [hzi, ha]
    simp only
    rw [P.mapH_cls _ q z hdz h2, hy i]
    exact ((P.cls_surj (B i) q).2.2.1 _ _ _ _).2 (by rw [hzi, sub_self]; exact Submodule.zero_mem _)

theorem const_H : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) (n : ℕ), Nonempty (CH.H F n ≃ₗ[R] CH.H (CH.elF ((Functor.const C).obj PUnit.{1}) F) n) := by
  intro R _ C _ F n
  let E : C ⥤ Type := (Functor.const C).obj PUnit.{1}
  let G : C ⥤ E.Elements :=
    { obj := fun T => ⟨T, PUnit.unit⟩
      map := fun φ => ⟨φ, rfl⟩ }
  let m : CH.Mor F (CH.elF E F) (RingHom.id R) := CH.Mor.restrict F (CategoryOfElements.π E)
  have hb : ∀ k, Function.Bijective (m.hom.f k) := by
    intro k
    constructor
    · intro x y h
      funext c
      exact congrFun h (c ⋙ G)
    · intro y
      exact ⟨fun c => y (c ⋙ G), funext fun s => rfl⟩
  exact ⟨LinearEquiv.ofBijective (m.hom.mapH n) (P.mapH_bij m.hom hb n)⟩

theorem mapH_sum {R : Type} [CommRing R] {A B : Cx.{w} R} {κ : Type} [Fintype κ] (ψ : Cx.Hom A B (RingHom.id R))
    (φ : κ → Cx.Hom A B (RingHom.id R)) (c : κ → ℤ) (q : ℕ)
    (h : ∀ x, ψ.f q x = ∑ k, c k • (φ k).f q x) (x : A.H q) :
    ψ.mapH q x = ∑ k, c k • (φ k).mapH q x := by
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
  have e : ψ.mapZ q z = ∑ k, c k • (φ k).mapZ q z := by
    refine Subtype.ext ?_
    rw [AddSubmonoidClass.coe_finsetSum]
    exact h z.1
  change Submodule.mkQ _ (ψ.mapZ q z) = ∑ k, c k • Submodule.mkQ _ ((φ k).mapZ q z)
  rw [e, map_sum]
  exact Finset.sum_congr rfl fun k _ => map_zsmul _ _ _

theorem col_comm : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {ι : Type} (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (F : C ⥤ ModuleCat.{w} R) (p q : ℕ) (x : ((dbl U hU F).col p).H q), (cechH F U q).d p (fun i => (tupM U hU F i).pull q x) = fun i => (tupM U hU F i).pull q ((colMap (dbl U hU F) p).mapH q x) := by
  intro R _ C _ ι U hU F p q x
  funext i
  have h1 := mapH_sum (colMap (dbl U hU F) p)
    (fun k : Fin (p + 2) => (CH.elMor (CH.cechMap (idxπ U hU) k.succAbove) F).hom) (fun k => (-1 : ℤ) ^ (k : ℕ)) q
    (fun a => Cos.d_apply ((CH.cechCos (idxπ U hU) F).cos q) p a) x
  rw [h1, map_sum, Cos.d_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul]
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
  rfl

end Pieces

section Nerve2

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {ι : Type}
  (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (F : C ⥤ ModuleCat.{w} R) {p q : ℕ}

def tupI (s : ComposableArrows (CH.cech (idxπ U hU) p).Elements q) : Fin (p + 1) → ι :=
  fun a => ((s.obj 0).2.1 a).1

theorem tupI_val (s : ComposableArrows (CH.cech (idxπ U hU) p).Elements q) (k : Fin (q + 1)) (a : Fin (p + 1)) :
    tupI U hU s a = ((s.obj k).2.1 a).1 :=
  congrArg (fun z : (CH.cech (idxπ U hU) p).obj (s.obj k).1 => (z.1 a).1) (s.map (homOfLE (Fin.zero_le k))).2

def tupL (s : ComposableArrows (CH.cech (idxπ U hU) p).Elements q) :
    ComposableArrows (capT U (tupI U hU s)).FullSubcategory q :=
  (capT U (tupI U hU s)).lift (s ⋙ CategoryOfElements.π _) fun k a =>
    hU _ (s.map (homOfLE (Fin.zero_le k))).1 ((s.obj 0).2.1 a).2

theorem tup_eval (f : CH.Cn (CH.elF (CH.cech (idxπ U hU) p) F) q)
    (s : ComposableArrows (CH.cech (idxπ U hU) p).Elements q) :
    @Eq (F.obj (s.obj (Fin.last q)).1) (f (tupL U hU s ⋙ tupF U hU (tupI U hU s))) (f s) :=
  ExtensionDiagram.mk_congr F f (s ⋙ CategoryOfElements.π _)
    (y := fun k => ((tupL U hU s ⋙ tupF U hU (tupI U hU s)).obj k).2) (y' := fun k => (s.obj k).2)
    (fun φ => ((tupL U hU s ⋙ tupF U hU (tupI U hU s)).map φ).2) (fun φ => (s.map φ).2)
    (funext fun k => Subtype.ext (funext fun a => Subtype.ext (tupI_val U hU s k a)))

theorem tup_bij : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {ι : Type} (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (F : C ⥤ ModuleCat.{w} R) (p q : ℕ), Function.Bijective (fun (x : CH.Cn (CH.elF (CH.cech (idxπ U hU) p) F) q) (i : Fin (p + 1) → ι) => (tupM U hU F i).pullC q x) := by
  intro R _ C _ ι U hU F p q
  constructor
  · intro x y h
    funext s
    have h1 := congrFun (congrFun h (tupI U hU s)) (tupL U hU s)
    exact (tup_eval U hU F x s).symm.trans (Eq.trans h1 (tup_eval U hU F y s))
  · intro y
    exact ⟨fun s => y (tupI U hU s) (tupL U hU s), funext fun i => funext fun c => rfl⟩

end Nerve2

section Lead

variable {R : Type} [CommRing R] (K : DCx.{w} R) {n : ℕ}

theorem dv_lead (x : ∀ p q, K.X p q) (hD : K.D x = 0) (a q : ℕ) (h0 : ∀ p q, p < a → x p q = 0) :
    K.dv a q (x a q) = 0 := by
  have h1 := congrFun (congrFun hD a) (q + 1)
  rw [DCx.D_apply] at h1
  have h2 : K.Dh x a (q + 1) = 0 := by
    cases a with
    | zero => rfl
    | succ a =>
      show K.dh a (q + 1) (x a (q + 1)) = 0
      rw [h0 a _ (by omega), map_zero]
  rw [h2, zero_add] at h1
  exact Auxfb.zsm_cancel a _ h1

theorem dh_lead (x : ∀ p q, K.X p q) (hD : K.D x = 0) (a q : ℕ) : K.dh a q (x a q) ∈ (K.col (a + 1)).B q := by
  have h1 := congrFun (congrFun hD (a + 1)) q
  rw [DCx.D_apply] at h1
  cases q with
  | zero =>
    show _ ∈ (⊥ : Submodule R _)
    rw [Submodule.mem_bot]
    simpa [DCx.Dh, DCx.Dv] using h1
  | succ q =>
    refine ⟨-((-1 : ℤ) ^ (a + 1) • x (a + 1) q), ?_⟩
    show K.dv (a + 1) q _ = _
    rw [map_neg, map_zsmul]
    exact (eq_neg_of_add_eq_zero_left h1).symm

theorem D_zero (z : K.tot.Z n) : K.D z.1.1 = 0 := congrArg Subtype.val (LinearMap.mem_ker.1 z.2)

def lead (a q : ℕ) : Zf K n a →ₗ[R] K.X a q where
  toFun z := z.1.1.1 a q
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def leadC (a q : ℕ) : Zf K n a →ₗ[R] (K.col a).H q :=
  (Submodule.mkQ _).comp ((lead K a q).codRestrict ((K.col a).Z q) fun z =>
    dv_lead K z.1.1.1 (D_zero K z.1) a q z.2)

theorem leadC_eq (a q : ℕ) (z : Zf K n a) (h) : leadC K a q z = (K.col a).cls (z.1.1.1 a q) h := rfl

theorem leadC_mem (a q : ℕ) (z : Zf K n a) : leadC K a q z ∈ (colH K q).Z a := by
  have hv : (K.col a).d q (z.1.1.1 a q) = 0 := dv_lead K z.1.1.1 (D_zero K z.1) a q z.2
  have hb : (K.col (a + 1)).d q ((colMap K a).f q (z.1.1.1 a q)) = 0 := by
    rw [(colMap K a).comm, hv, map_zero]
  change (colMap K a).mapH q (leadC K a q z) = 0
  rw [leadC_eq K a q z hv, P.mapH_cls _ q _ hv hb, (P.cls_surj _ q).2.1]
  exact dh_lead K z.1.1.1 (D_zero K z.1) a q

def leadE (a q : ℕ) : Zf K n a →ₗ[R] (colH K q).H a :=
  (Submodule.mkQ _).comp ((leadC K a q).codRestrict ((colH K q).Z a) (leadC_mem K a q))

theorem leadE_eq (a q : ℕ) (z : Zf K n a) : leadE K a q z = (colH K q).cls (leadC K a q z) (leadC_mem K a q z) := rfl

theorem lower {a : ℕ} (z : Zf K n a) (W : ∀ p q, K.X p q) (hs : ∀ p q, p + q + 1 ≠ n → W p q = 0)
    (hW : ∀ p r, p < a + 1 → (z.1.1.1 - K.D W) p r = 0) : clsZ K n a z ∈ Ff K n (a + 1) := by
  have hDW : K.D W ∈ K.T n := Auxfb.Dmem' K n W hs
  have hT : z.1.1.1 - K.D W ∈ K.T n := Submodule.sub_mem _ z.1.1.2 hDW
  have hc : K.tot.d n ⟨_, hT⟩ = 0 := Subtype.ext (by
    change K.D (z.1.1.1 - K.D W) = 0
    rw [map_sub, K.DD, D_zero K z.1, sub_zero])
  refine ⟨⟨⟨⟨_, hT⟩, hc⟩, hW⟩, ?_⟩
  refine ((P.cls_surj K.tot n).2.2.1 _ _ hc z.1.2).2 ?_
  have e : z.1.1.1 - K.D W - z.1.1.1 = K.D (-W) := by rw [map_neg]; abel
  cases n with
  | zero =>
    have hW0 : W = 0 := funext fun p => funext fun q => hs p q (by omega)
    show _ ∈ (⊥ : Submodule R _)
    rw [Submodule.mem_bot]
    refine Subtype.ext ?_
    change z.1.1.1 - K.D W - z.1.1.1 = 0
    rw [hW0]; simp
  | succ m =>
    have hWT : -W ∈ K.T m := Submodule.neg_mem _ fun p q h => hs p q (by omega)
    exact ⟨⟨_, hWT⟩, Subtype.ext e.symm⟩

theorem lower_fin (x : ∀ p q, K.X p q) (hT : x ∈ K.T n) {a q : ℕ} (haq : a + q = n) (h0 : ∀ p q, p < a → x p q = 0)
    (W : ∀ p q, K.X p q) (hW : ∀ p r, p < a + 1 → K.D W p r = K.sgl a q (x a q) p r) :
    ∀ p r, p < a + 1 → (x - K.D W) p r = 0 := by
  intro p r hp
  rw [Pi.sub_apply, Pi.sub_apply, hW p r hp]
  by_cases h : p = a ∧ r = q
  · obtain ⟨rfl, rfl⟩ := h
    rw [K.sgl_self, sub_self]
  · rw [K.sgl_ne _ (by omega), sub_zero]
    by_cases hpa : p < a
    · exact h0 p r hpa
    · exact hT p r (by omega)

theorem lower_vert (x : ∀ p q, K.X p q) (hT : x ∈ K.T n) {a q : ℕ} (haq : a + q = n) (h0 : ∀ p q, p < a → x p q = 0)
    (v₁ : K.X a q) (W₁ : ∀ p q, K.X p q) (hs : ∀ p q, p + q + 1 ≠ n → W₁ p q = 0) (hW₁ : K.D W₁ = K.sgl a q v₁)
    (hv : x a q - v₁ ∈ (K.col a).B q) :
    ∃ W : ∀ p q, K.X p q, (∀ p q, p + q + 1 ≠ n → W p q = 0) ∧ ∀ p r, p < a + 1 → (x - K.D W) p r = 0 := by
  cases q with
  | zero =>
    have h1 : x a 0 = v₁ := sub_eq_zero.1 ((Submodule.mem_bot R).1 hv)
    exact ⟨W₁, hs, lower_fin K x hT haq h0 W₁ fun p r _ => by rw [hW₁, h1]⟩
  | succ q =>
    obtain ⟨u, hu⟩ := hv
    have hu' : K.dv a q u = x a (q + 1) - v₁ := hu
    refine ⟨W₁ + (-1 : ℤ) ^ a • K.sgl a q u, fun p r h => ?_, lower_fin K x hT haq h0 _ fun p r hp => ?_⟩
    · show W₁ p r + (-1 : ℤ) ^ a • K.sgl a q u p r = 0
      rw [hs p r h, K.sgl_ne u (by omega)]
      simp
    · have hsq : ((-1 : ℤ) ^ a * (-1) ^ a) = 1 := by rw [← mul_pow]; simp
      rw [map_add, map_zsmul, K.D_sgl, hW₁, hu', smul_add, smul_smul, hsq, one_smul, map_sub]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
      rw [K.sgl_ne (K.dh a q u) (Or.inl (by omega) : p ≠ a + 1 ∨ r ≠ q)]
      simp

theorem psi_exists : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (n a q : ℕ), a + q = n → ∃ ψ : Zf K n a →ₗ[R] (colH K q).H a, ∀ z, ψ z = 0 → clsZ K n a z ∈ Ff K n (a + 1) := by
  intro R _ K n a q haq
  refine ⟨leadE K a q, fun z hz => ?_⟩
  have hv : (K.col a).d q (z.1.1.1 a q) = 0 := dv_lead K z.1.1.1 (D_zero K z.1) a q z.2
  have hB : leadC K a q z ∈ (colH K q).B a :=
    ((P.cls_surj (colH K q) a).2.1 _ _).1 ((leadE_eq K a q z).symm.trans hz)
  have hx : z.1.1.1 ∈ K.T n := z.1.1.2
  have h0 : ∀ p q, p < a → z.1.1.1 p q = 0 := z.2
  suffices h : ∃ (v₁ : K.X a q) (W₁ : ∀ p q, K.X p q), (∀ p q, p + q + 1 ≠ n → W₁ p q = 0) ∧
      K.D W₁ = K.sgl a q v₁ ∧ z.1.1.1 a q - v₁ ∈ (K.col a).B q by
    obtain ⟨v₁, W₁, hs, hW₁, hd⟩ := h
    obtain ⟨W, hW, hl⟩ := lower_vert K _ hx haq h0 v₁ W₁ hs hW₁ hd
    exact lower K z W hW hl
  cases a with
  | zero =>
    refine ⟨0, 0, fun _ _ _ => rfl, by simp, ?_⟩
    have h1 : leadC K 0 q z = 0 := (Submodule.mem_bot R).1 hB
    rw [leadC_eq K 0 q z hv, (P.cls_surj _ q).2.1] at h1
    simpa using h1
  | succ a =>
    obtain ⟨c, hc⟩ := hB
    obtain ⟨y, hy, rfl⟩ := (P.cls_surj (K.col a) q).1 c
    have hb : (K.col (a + 1)).d q ((colMap K a).f q y) = 0 := by
      rw [(colMap K a).comm, hy, map_zero]
    have h2 : (colMap K a).mapH q ((K.col a).cls y hy) = leadC K (a + 1) q z := hc
    rw [P.mapH_cls _ q y hy hb, leadC_eq K (a + 1) q z hv] at h2
    have h3 := ((P.cls_surj (K.col (a + 1)) q).2.2.1 _ _ hv hb).1 h2.symm
    refine ⟨K.dh a q y, K.sgl a q y, fun p r h => K.sgl_ne y (by omega), ?_, h3⟩
    rw [K.D_sgl, show K.dv a q y = 0 from hy, map_zero, smul_zero, add_zero]

end Lead

section Main

variable {R : Type} [CommRing R]

theorem Ff_top_subsingleton (K : DCx.{w} R) (n : ℕ) : Subsingleton (Ff K n (n + 1)) := by
  have h0 : ∀ z : Zf K n (n + 1), z = 0 := by
    intro z
    refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun p => funext fun q => ?_)))
    by_cases hp : p < n + 1
    · exact z.2 p q hp
    · exact z.1.1.2 p q (by omega)
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, a, rfl⟩ := x
  obtain ⟨y, b, rfl⟩ := y
  rw [h0 a, h0 b]

theorem serre_Ff (𝒮 : Serre.{w} R) (K : DCx.{w} R) (n : ℕ)
    (h : ∀ p q, p + q = n → 𝒮.P ((colH K q).H p)) : ∀ k a, a + k = n + 1 → 𝒮.P (Ff K n a) := by
  intro k
  induction k with
  | zero =>
    intro a ha
    obtain rfl : a = n + 1 := by omega
    exact 𝒮.zero _ (Ff_top_subsingleton K n)
  | succ k ih =>
    intro a ha
    obtain ⟨q, hq⟩ : ∃ q, a + q = n := ⟨n - a, by omega⟩
    obtain ⟨ψ, hψ⟩ := psi_exists K n a q hq
    exact serre_step 𝒮 (clsZ K n a) ψ (Ff K n (a + 1)) hψ (ih (a + 1) (by omega)) (h a q hq)

theorem serre_tot (𝒮 : Serre.{w} R) (K : DCx.{w} R) (n : ℕ)
    (h : ∀ p q, p + q = n → 𝒮.P ((colH K q).H p)) : 𝒮.P (K.tot.H n) := by
  refine serre_of_surjective 𝒮 (Ff K n 0).subtype ?_ (serre_Ff 𝒮 K n h (n + 1) 0 (by omega))
  intro x
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
  exact ⟨⟨_, ⟨z, fun p q hp => absurd hp (Nat.not_lt_zero p)⟩, rfl⟩, rfl⟩

variable {C : Type u} [Category.{v} C] {ι : Type}

def colCmp (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (F : C ⥤ ModuleCat.{w} R) (q : ℕ) :
    Cx.Hom (colH (dbl U hU F) q) (cechH F U q).cx (RingHom.id R) where
  f p := LinearMap.pi fun i => (tupM U hU F i).pull q
  comm p x := col_comm U hU F p q x

theorem colCmp_bij (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (F : C ⥤ ModuleCat.{w} R) (p q : ℕ) :
    Function.Bijective ((colCmp U hU F q).f p) :=
  pi_H_bij (fun i : Fin (p + 1) → ι => CH.cx ((capT U i).ι ⋙ F)) (fun i => (tupM U hU F i).hom)
    (fun q => tup_bij U hU F p q) q

end Main

theorem serre_cech : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) {ι : Type}
    (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (hc : ∀ T, ∃ α, U α T) (𝒮 : Serre.{1} R) (n : ℕ),
    (∀ p q, p + q = n → 𝒮.P ((cechH F U q).cx.H p)) → 𝒮.P (CH.H F n) := by
  intro R _ C _ F ι U hU hc 𝒮 n h
  have hs : ∀ T, Function.Surjective ((idxπ U hU).app T) := by
    intro T x
    obtain ⟨α, hα⟩ := hc T
    exact ⟨⟨α, hα⟩, rfl⟩
  have htot : 𝒮.P ((dbl U hU F).tot.H n) := by
    refine serre_tot 𝒮 _ n fun p q hpq => ?_
    have hb := P.mapH_bij (colCmp U hU F q) (fun p => colCmp_bij U hU F p q) p
    exact serre_of_equiv 𝒮 (LinearEquiv.ofBijective _ hb).symm (h p q hpq)
  have hb := P.cech_desc (idxπ U hU) F hs n
  obtain ⟨e⟩ := const_H F n
  exact serre_of_equiv 𝒮 (e.trans (LinearEquiv.ofBijective _ hb)).symm htot

end GlobalTheory.CompanionTheory.CechSerre
