import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.TateTwists.EtaleTensorTripleProductOfFamilyAndLeibniz

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.EtaleFoundations.TensTriFamPf

def SecGlue : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg

variable {R : Type} [CommRing R]

lemma res_id {F : Shv R} {U : Scheme.{0}} (a : Sec F U) : Sec.res (𝟙 U) a = a := by
  simp [Sec.res]

lemma res_comp {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res (k ≫ g) a = Sec.res k (Sec.res g a) := by
  simp [Sec.res]

lemma res_add {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec F U) :
    Sec.res g (a + b) = Sec.res g a + Sec.res g b := map_add _ _ _

lemma res_smul {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (r : ULift.{1} R) (a : Sec F U) :
    Sec.res g (r • a) = r • Sec.res g a := map_smul _ _ _

lemma loc_inter {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hSP⟩ := hP
  obtain ⟨S', hS', hSQ⟩ := hQ
  exact ⟨S ⊓ S', Scheme.etaleTopology.intersection_covering hS hS', fun V g hg => ⟨hSP V g hg.1, hSQ V g hg.2⟩⟩

lemma loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hSP⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (hSP V g hg)⟩

lemma loc_pull {U V : Scheme.{0}} (k : V ⟶ U) {P : ∀ W : Scheme.{0}, (W ⟶ U) → Prop} (hP : Loc U P) :
    Loc V fun W h => P W (h ≫ k) := by
  obtain ⟨S, hS, hSP⟩ := hP
  exact ⟨S.pullback k, Scheme.etaleTopology.pullback_stable k hS, fun W h hh => hSP W _ hh⟩

section
variable {I J K T M L : Cx R}

lemma lift_res (τ : Pair I J T) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    τ.lift V w (Tens.res g w x) = Sec.res g (τ.lift U w x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of p y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [← DirectSum.lof_eq_of (ULift.{1} R)]
      simp only [Pair.lift, Tens.res, DirectSum.lmap_lof, DirectSum.toModule_lof, TensorProduct.map_tmul,
        TensorProduct.lift.tmul]
      exact (τ.nat g _ _ _ _ a b).symm
    | add y y' hy hy' => simp only [map_add, hy, hy']
  | add x x' hx hx' => simp only [map_add, hx, hx']

lemma lift_single (τ : Pair I J T) (U : Scheme.{0}) (s t st : ℤ) (h1 : s + t = st) (a : Sec (I.X s) U)
    (b : Sec (J.X t) U) :
    τ.lift U st (DirectSum.of _ (⟨(s, t), h1⟩ : {p : ℤ × ℤ // p.1 + p.2 = st}) (a ⊗ₜ[ULift.{1} R] b)) =
      τ.mul U s t st h1 a b := by
  rw [← DirectSum.lof_eq_of (ULift.{1} R)]
  simp only [Pair.lift, DirectSum.toModule_lof, TensorProduct.lift.tmul]

noncomputable def Bp (μ' : Pair J K M) (ν' : Pair I M L) (V : Scheme.{0}) (st u w : ℤ) (h2 : st + u = w)
    (p : {p : ℤ × ℤ // p.1 + p.2 = st}) :
    Sec (I.X p.1.1) V →ₗ[ULift.{1} R] Sec (J.X p.1.2) V →ₗ[ULift.{1} R] (Sec (K.X u) V →ₗ[ULift.{1} R] Sec (L.X w) V) :=
  LinearMap.mk₂ (ULift.{1} R)
    (fun a b => (ν'.mul V p.1.1 (p.1.2 + u) w (by have := p.2; omega) a) ∘ₗ (μ'.mul V p.1.2 u (p.1.2 + u) rfl b))
    (fun a a' b => LinearMap.ext fun c => by simp)
    (fun r a b => LinearMap.ext fun c => by simp)
    (fun a b b' => LinearMap.ext fun c => by simp)
    (fun r a b => LinearMap.ext fun c => by simp)

noncomputable def B (μ' : Pair J K M) (ν' : Pair I M L) (V : Scheme.{0}) (st u w : ℤ) (h2 : st + u = w) :
    Tens I J V st →ₗ[ULift.{1} R] (Sec (K.X u) V →ₗ[ULift.{1} R] Sec (L.X w) V) :=
  DirectSum.toModule _ _ _ fun p => TensorProduct.lift (Bp μ' ν' V st u w h2 p)

lemma B_single (μ' : Pair J K M) (ν' : Pair I M L) (V : Scheme.{0}) (s t st u w : ℤ) (h1 : s + t = st)
    (h2 : st + u = w) (a : Sec (I.X s) V) (b : Sec (J.X t) V) (c : Sec (K.X u) V) :
    B μ' ν' V st u w h2 (DirectSum.of _ (⟨(s, t), h1⟩ : {p : ℤ × ℤ // p.1 + p.2 = st}) (a ⊗ₜ[ULift.{1} R] b)) c =
      ν'.mul V s (t + u) w (by omega) a (μ'.mul V t u (t + u) rfl b c) := by
  rw [← DirectSum.lof_eq_of (ULift.{1} R)]
  simp only [B, Bp, DirectSum.toModule_lof, TensorProduct.lift.tmul, LinearMap.mk₂_apply, LinearMap.comp_apply]

lemma B_res (μ' : Pair J K M) (ν' : Pair I M L) {W V : Scheme.{0}} (k : W ⟶ V) (st u w : ℤ) (h2 : st + u = w)
    (x : Tens I J V st) (c : Sec (K.X u) V) :
    Sec.res k (B μ' ν' V st u w h2 x c) = B μ' ν' W st u w h2 (Tens.res k st x) (Sec.res k c) := by
  induction x using DirectSum.induction_on with
  | zero => simp [Sec.res]
  | of p y =>
    induction y using TensorProduct.induction_on with
    | zero => simp [Sec.res]
    | tmul a b =>
      rw [← DirectSum.lof_eq_of (ULift.{1} R)]
      simp only [B, Bp, Tens.res, DirectSum.lmap_lof, DirectSum.toModule_lof, TensorProduct.map_tmul,
        TensorProduct.lift.tmul, LinearMap.mk₂_apply, LinearMap.comp_apply]
      rw [ν'.nat, μ'.nat]
    | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']

end

section
variable {I J K T M L : Cx R}

lemma B_wd (hg : SecGlue) (τ : Pair I J T) (hτ : τ.IsTensor) (μ' : Pair J K M) (ν' : Pair I M L)
    {V : Scheme.{0}} {st u w : ℤ} {h2 : st + u = w} {x y : Tens I J V st} (c : Sec (K.X u) V)
    (h : τ.lift V st x = τ.lift V st y) : B μ' ν' V st u w h2 x c = B μ' ν' V st u w h2 y c := by
  have h0 : τ.lift V st (x - y) = 0 := by rw [map_sub, h, sub_self]
  refine (hg R (L.X w) V).1 _ _ (loc_mono (hτ.2 V st (x - y) h0) fun W k hk => ?_)
  rw [map_sub, sub_eq_zero] at hk
  rw [B_res, B_res, hk]

lemma exists_m (hg : SecGlue) (τ : Pair I J T) (hτ : τ.IsTensor) (μ' : Pair J K M) (ν' : Pair I M L)
    (U : Scheme.{0}) (st u w : ℤ) (h2 : st + u = w) (a : Sec (T.X st) U) (c : Sec (K.X u) U) :
    ∃ m0 : Sec (L.X w) U, ∀ (V : Scheme.{0}) (g : V ⟶ U) (x : Tens I J V st), τ.lift V st x = Sec.res g a →
      Sec.res g m0 = B μ' ν' V st u w h2 x (Sec.res g c) := by
  obtain ⟨S, hS, hP⟩ := hτ.1 U st a
  obtain ⟨m0, hm0⟩ := (hg R (L.X w) U).2 S hS
    (fun V g hg' => B μ' ν' V st u w h2 (hP V g hg').choose (Sec.res g c)) (by
      intro V W g k hg'
      rw [B_res, res_comp k g c]
      apply B_wd hg τ hτ μ' ν'
      rw [lift_res, (hP V g hg').choose_spec, (hP W (k ≫ g) (S.downward_closed hg' k)).choose_spec, res_comp])
  refine ⟨m0, fun V g x hx => ?_⟩
  apply (hg R (L.X w) V).1
  refine loc_mono (loc_pull g (P := fun W h => S.arrows h) ⟨S, hS, fun _ _ h => h⟩) fun W k hk => ?_
  rw [← res_comp, hm0 W (k ≫ g) hk, B_res, ← res_comp]
  apply B_wd hg τ hτ μ' ν'
  rw [lift_res, (hP W (k ≫ g) hk).choose_spec, hx, res_comp]

noncomputable def mraw (hg : SecGlue) (τ : Pair I J T) (hτ : τ.IsTensor) (μ' : Pair J K M) (ν' : Pair I M L)
    (U : Scheme.{0}) (st u w : ℤ) (h2 : st + u = w) (a : Sec (T.X st) U) (c : Sec (K.X u) U) : Sec (L.X w) U :=
  (exists_m hg τ hτ μ' ν' U st u w h2 a c).choose

variable (hg : SecGlue) (τ : Pair I J T) (hτ : τ.IsTensor) (μ' : Pair J K M) (ν' : Pair I M L)

lemma res_mraw_eq_of_lift {U : Scheme.{0}} {st u w : ℤ} {h2 : st + u = w} (a : Sec (T.X st) U) (c : Sec (K.X u) U)
    {V : Scheme.{0}} (g : V ⟶ U) (x : Tens I J V st) (hx : τ.lift V st x = Sec.res g a) :
    Sec.res g (mraw hg τ hτ μ' ν' U st u w h2 a c) = B μ' ν' V st u w h2 x (Sec.res g c) :=
  (exists_m hg τ hτ μ' ν' U st u w h2 a c).choose_spec V g x hx

lemma mraw_add_a {U : Scheme.{0}} {st u w : ℤ} {h2 : st + u = w} (a a' : Sec (T.X st) U) (c : Sec (K.X u) U) :
    mraw hg τ hτ μ' ν' U st u w h2 (a + a') c = mraw hg τ hτ μ' ν' U st u w h2 a c + mraw hg τ hτ μ' ν' U st u w h2 a' c := by
  apply (hg R (L.X w) U).1
  refine loc_mono (loc_inter (hτ.1 U st a) (hτ.1 U st a')) fun V g hV => ?_
  obtain ⟨⟨x, hx⟩, ⟨x', hx'⟩⟩ := hV
  rw [res_add, res_mraw_eq_of_lift hg τ hτ μ' ν' (a + a') c g (x + x') (by rw [map_add, hx, hx', res_add]),
    res_mraw_eq_of_lift hg τ hτ μ' ν' a c g x hx, res_mraw_eq_of_lift hg τ hτ μ' ν' a' c g x' hx', map_add, LinearMap.add_apply]

lemma mraw_smul_a {U : Scheme.{0}} {st u w : ℤ} {h2 : st + u = w} (r : ULift.{1} R) (a : Sec (T.X st) U) (c : Sec (K.X u) U) :
    mraw hg τ hτ μ' ν' U st u w h2 (r • a) c = r • mraw hg τ hτ μ' ν' U st u w h2 a c := by
  apply (hg R (L.X w) U).1
  refine loc_mono (hτ.1 U st a) fun V g hV => ?_
  obtain ⟨x, hx⟩ := hV
  rw [res_smul, res_mraw_eq_of_lift hg τ hτ μ' ν' (r • a) c g (r • x) (by rw [map_smul, hx, res_smul]),
    res_mraw_eq_of_lift hg τ hτ μ' ν' a c g x hx, map_smul, LinearMap.smul_apply]

lemma mraw_add_c {U : Scheme.{0}} {st u w : ℤ} {h2 : st + u = w} (a : Sec (T.X st) U) (c c' : Sec (K.X u) U) :
    mraw hg τ hτ μ' ν' U st u w h2 a (c + c') = mraw hg τ hτ μ' ν' U st u w h2 a c + mraw hg τ hτ μ' ν' U st u w h2 a c' := by
  apply (hg R (L.X w) U).1
  refine loc_mono (hτ.1 U st a) fun V g hV => ?_
  obtain ⟨x, hx⟩ := hV
  rw [res_add, res_mraw_eq_of_lift hg τ hτ μ' ν' a (c + c') g x hx, res_mraw_eq_of_lift hg τ hτ μ' ν' a c g x hx,
    res_mraw_eq_of_lift hg τ hτ μ' ν' a c' g x hx, res_add, map_add]

lemma mraw_smul_c {U : Scheme.{0}} {st u w : ℤ} {h2 : st + u = w} (r : ULift.{1} R) (a : Sec (T.X st) U) (c : Sec (K.X u) U) :
    mraw hg τ hτ μ' ν' U st u w h2 a (r • c) = r • mraw hg τ hτ μ' ν' U st u w h2 a c := by
  apply (hg R (L.X w) U).1
  refine loc_mono (hτ.1 U st a) fun V g hV => ?_
  obtain ⟨x, hx⟩ := hV
  rw [res_smul, res_mraw_eq_of_lift hg τ hτ μ' ν' a (r • c) g x hx, res_mraw_eq_of_lift hg τ hτ μ' ν' a c g x hx, res_smul, map_smul]

lemma mraw_nat {V U : Scheme.{0}} (g' : V ⟶ U) {st u w : ℤ} {h2 : st + u = w} (a : Sec (T.X st) U) (c : Sec (K.X u) U) :
    Sec.res g' (mraw hg τ hτ μ' ν' U st u w h2 a c) = mraw hg τ hτ μ' ν' V st u w h2 (Sec.res g' a) (Sec.res g' c) := by
  apply (hg R (L.X w) V).1
  refine loc_mono (hτ.1 V st (Sec.res g' a)) fun W k hW => ?_
  obtain ⟨x, hx⟩ := hW
  rw [← res_comp, res_mraw_eq_of_lift hg τ hτ μ' ν' a c (k ≫ g') x (by rw [hx, res_comp]),
    res_mraw_eq_of_lift hg τ hτ μ' ν' (Sec.res g' a) (Sec.res g' c) k x hx, res_comp]

lemma mraw_eq (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w) (h3 : t + u = tu)
    (h4 : s + tu = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U) (c : Sec (K.X u) U) :
    mraw hg τ hτ μ' ν' U st u w h2 (τ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c) := by
  subst h3
  have h := res_mraw_eq_of_lift hg τ hτ μ' ν' (h2 := h2) (τ.mul U s t st h1 a b) c (𝟙 U)
    (DirectSum.of _ (⟨(s, t), h1⟩ : {p : ℤ × ℤ // p.1 + p.2 = st}) (a ⊗ₜ[ULift.{1} R] b))
    (by rw [lift_single, res_id])
  rw [res_id, res_id] at h
  rw [h, B_single]

noncomputable def mfam (U : Scheme.{0}) (st u w : ℤ) (h2 : st + u = w) :
    Sec (T.X st) U →ₗ[ULift.{1} R] Sec (K.X u) U →ₗ[ULift.{1} R] Sec (L.X w) U :=
  LinearMap.mk₂ (ULift.{1} R) (mraw hg τ hτ μ' ν' U st u w h2)
    (mraw_add_a hg τ hτ μ' ν') (mraw_smul_a hg τ hτ μ' ν') (mraw_add_c hg τ hτ μ' ν') (mraw_smul_c hg τ hτ μ' ν')

end

end LateralTheory.EtaleFoundations.TensTriFamPf

open LateralTheory.EtaleFoundations.TensTriFamPf in

theorem LateralTheory.EtaleFoundations.etale_tensor_triple_product_family_of_gluing (hglue : SecGlue) : LateralTheory.EtaleFoundations.EtaleTensorTripleProductFamilyExists := by
  intro R _ I J K T τ hτ M L μ' ν'
  refine ⟨fun U st u w h2 => mfam hglue τ hτ μ' ν' U st u w h2, ?_, ?_⟩
  · intro V U g s t w h a b
    exact mraw_nat hglue τ hτ μ' ν' g a b
  · intro U s t u st tu w h1 h2 h3 h4 a b c
    exact mraw_eq hglue τ hτ μ' ν' U s t u st tu w h1 h2 h3 h4 a b c
