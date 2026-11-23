import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRules
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace GlobalTheory.EtC
namespace TensAssoc

variable {R : Type} [CommRing R] {I J K T M L : Cx R}

noncomputable def bil (μ' : Pair J K M) (ν' : Pair I M L) (st u w : ℤ) (h : st + u = w) (V : Scheme.{0})
    (c : Sec (K.X u) V) (p : {p : ℤ × ℤ // p.1 + p.2 = st}) :
    Sec (I.X p.1.1) V →ₗ[ULift.{1} R] Sec (J.X p.1.2) V →ₗ[ULift.{1} R] Sec (L.X w) V :=
  (ν'.mul V p.1.1 (p.1.2 + u) w (by have := p.2; omega)).compl₂ ((μ'.mul V p.1.2 u (p.1.2 + u) rfl).flip c)

noncomputable def B (μ' : Pair J K M) (ν' : Pair I M L) (st u w : ℤ) (h : st + u = w) (V : Scheme.{0})
    (c : Sec (K.X u) V) : Tens I J V st →ₗ[ULift.{1} R] Sec (L.X w) V := by
  classical
  exact DirectSum.toModule _ _ _ fun p => TensorProduct.lift (bil μ' ν' st u w h V c p)

theorem B_lof (μ' : Pair J K M) (ν' : Pair I M L) (st u w : ℤ) (h : st + u = w) (V : Scheme.{0})
    (c : Sec (K.X u) V) (p : {p : ℤ × ℤ // p.1 + p.2 = st}) (a : Sec (I.X p.1.1) V) (b : Sec (J.X p.1.2) V) :
    B μ' ν' st u w h V c (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = st} =>
      Sec (I.X p.1.1) V ⊗[ULift.{1} R] Sec (J.X p.1.2) V) p (a ⊗ₜ b)) =
      ν'.mul V p.1.1 (p.1.2 + u) w (by have := p.2; omega) a (μ'.mul V p.1.2 u (p.1.2 + u) rfl b c) := by
  unfold B
  rw [DirectSum.toModule_lof, TensorProduct.lift.tmul]
  rfl

theorem lift_lof (τ : Pair I J T) (V : Scheme.{0}) (st : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = st})
    (a : Sec (I.X p.1.1) V) (b : Sec (J.X p.1.2) V) :
    τ.lift V st (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = st} =>
      Sec (I.X p.1.1) V ⊗[ULift.{1} R] Sec (J.X p.1.2) V) p (a ⊗ₜ b)) = τ.mul V p.1.1 p.1.2 st p.2 a b := by
  unfold Pair.lift
  rw [DirectSum.toModule_lof, TensorProduct.lift.tmul]

theorem tres_lof {V U : Scheme.{0}} (g : V ⟶ U) (st : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = st})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    Tens.res (I := I) (J := J) g st (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = st} =>
      Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p (a ⊗ₜ b)) =
      DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = st} =>
      Sec (I.X p.1.1) V ⊗[ULift.{1} R] Sec (J.X p.1.2) V) p (Sec.res g a ⊗ₜ Sec.res g b) := by
  unfold Tens.res
  rw [DirectSum.lmap_lof, TensorProduct.map_tmul]

theorem tens_ind {V : Scheme.{0}} {st : ℤ} {P : Tens I J V st → Prop} (x : Tens I J V st) (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y))
    (hof : ∀ (p : {p : ℤ × ℤ // p.1 + p.2 = st}) (a : Sec (I.X p.1.1) V) (b : Sec (J.X p.1.2) V),
      P (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = st} =>
      Sec (I.X p.1.1) V ⊗[ULift.{1} R] Sec (J.X p.1.2) V) p (a ⊗ₜ b))) : P x := by
  induction x using DirectSum.induction_on with
  | zero => exact h0
  | add x y hx hy => exact hadd x y hx hy
  | of p m =>
    induction m using TensorProduct.induction_on with
    | zero => simpa using h0
    | tmul a b => exact hof p a b
    | add m m' hm hm' =>
      rw [map_add]
      exact hadd _ _ hm hm'

end TensAssoc
end GlobalTheory.EtC

namespace GlobalTheory.EtC
namespace TensAssoc

variable {R : Type} [CommRing R] {I J K T M L : Cx R}

theorem res_res' {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res k (Sec.res g a) = Sec.res (k ≫ g) a := by
  simp [Sec.res]

theorem res_add' {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a a' : Sec F U) :
    Sec.res g (a + a') = Sec.res g a + Sec.res g a' := map_add _ _ _

theorem res_smul' {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (r : ULift.{1} R) (a : Sec F U) :
    Sec.res g (r • a) = r • Sec.res g a := map_smul _ _ _

theorem res_map' {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.res g (Sec.map φ a) = Sec.map φ (Sec.res g a) := by
  have := congrArg (fun f => f.hom a) (φ.hom.naturality g.op)
  simpa [Sec.res, Sec.map] using this.symm

theorem lift_nat (τ : Pair I J T) {V U : Scheme.{0}} (g : V ⟶ U) (st : ℤ) (x : Tens I J U st) :
    Sec.res g (τ.lift U st x) = τ.lift V st (Tens.res g st x) := by
  induction x using tens_ind with
  | h0 => simp
  | hadd x y hx hy => rw [map_add, res_add', hx, hy, map_add, map_add]
  | hof p a b => rw [lift_lof, tres_lof, lift_lof, τ.nat]

theorem B_nat (μ' : Pair J K M) (ν' : Pair I M L) (st u w : ℤ) (h : st + u = w) {V U : Scheme.{0}} (g : V ⟶ U)
    (c : Sec (K.X u) U) (x : Tens I J U st) :
    Sec.res g (B μ' ν' st u w h U c x) = B μ' ν' st u w h V (Sec.res g c) (Tens.res g st x) := by
  induction x using tens_ind with
  | h0 => simp
  | hadd x y hx hy => rw [map_add, res_add', hx, hy, map_add, map_add]
  | hof p a b => rw [B_lof, tres_lof, B_lof, ν'.nat, μ'.nat]

theorem B_add_c (μ' : Pair J K M) (ν' : Pair I M L) (st u w : ℤ) (h : st + u = w) (V : Scheme.{0})
    (c c' : Sec (K.X u) V) (x : Tens I J V st) :
    B μ' ν' st u w h V (c + c') x = B μ' ν' st u w h V c x + B μ' ν' st u w h V c' x := by
  induction x using tens_ind with
  | h0 => simp
  | hadd x y hx hy => rw [map_add, hx, hy, map_add, map_add]; abel
  | hof p a b => rw [B_lof, B_lof, B_lof, map_add, map_add]

theorem B_smul_c (μ' : Pair J K M) (ν' : Pair I M L) (st u w : ℤ) (h : st + u = w) (V : Scheme.{0})
    (r : ULift.{1} R) (c : Sec (K.X u) V) (x : Tens I J V st) :
    B μ' ν' st u w h V (r • c) x = r • B μ' ν' st u w h V c x := by
  induction x using tens_ind with
  | h0 => simp
  | hadd x y hx hy => rw [map_add, hx, hy, map_add, smul_add]
  | hof p a b => rw [B_lof, B_lof, map_smul, map_smul]

section Glue
variable {τ : Pair I J T} (hτ : τ.IsTensor) (μ' : Pair J K M) (ν' : Pair I M L) (st u w : ℤ) (h : st + u = w)

include hτ in
theorem key {V : Scheme.{0}} (c : Sec (K.X u) V) (x x' : Tens I J V st) (hx : τ.lift V st x = τ.lift V st x') :
    B μ' ν' st u w h V c x = B μ' ν' st u w h V c x' := by
  obtain ⟨S, hS, hz⟩ := hτ.2 V st (x - x') (by rw [map_sub, hx, sub_self])
  refine (sec_ext_glue R (L.X w) V).1 _ _ ⟨S, hS, fun W k hk => ?_⟩
  try dsimp only
  rw [B_nat, B_nat]
  have := hz W k hk
  try dsimp only at this
  rw [map_sub, sub_eq_zero] at this
  rw [this]

variable (τ) in

def Ch (U : Scheme.{0}) (y : Sec (T.X st) U) (c : Sec (K.X u) U) (a : Sec (L.X w) U) : Prop :=
  ∀ (V : Scheme.{0}) (g : V ⟶ U) (x : Tens I J V st), τ.lift V st x = Sec.res g y →
    Sec.res g a = B μ' ν' st u w h V (Sec.res g c) x

include hτ in
theorem ch_loc {U : Scheme.{0}} (y : Sec (T.X st) U) (c : Sec (K.X u) U) (a : Sec (L.X w) U)
    (hl : Loc U fun V g => ∃ x, τ.lift V st x = Sec.res g y ∧ Sec.res g a = B μ' ν' st u w h V (Sec.res g c) x) :
    Ch τ μ' ν' st u w h U y c a := by
  intro V g x hx
  obtain ⟨S, hS, hS'⟩ := loc_pullback U V g _ hl
  refine (sec_ext_glue R (L.X w) V).1 _ _ ⟨S, hS, fun W k hk => ?_⟩
  obtain ⟨x', hx'1, hx'2⟩ := hS' W k hk
  try dsimp only
  rw [res_res', hx'2, B_nat, res_res']
  apply key hτ
  rw [hx'1, ← lift_nat, hx, res_res']

include hτ in
theorem ch_exists (U : Scheme.{0}) (y : Sec (T.X st) U) (c : Sec (K.X u) U) :
    ∃ a, Ch τ μ' ν' st u w h U y c a := by
  obtain ⟨S, hS, hl⟩ := hτ.1 U st y
  let s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec (L.X w) V :=
    fun V g hg => B μ' ν' st u w h V (Sec.res g c) (hl V g hg).choose
  have hs : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g),
      Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k) := by
    intro V W g k hg
    simp only [s]
    rw [B_nat, res_res']
    apply key hτ
    rw [← lift_nat, (hl V g hg).choose_spec, (hl W (k ≫ g) (S.downward_closed hg k)).choose_spec, res_res']
  obtain ⟨a, ha⟩ := (sec_ext_glue R (L.X w) U).2 S hS s hs
  exact ⟨a, ch_loc hτ μ' ν' st u w h y c a
    ⟨S, hS, fun V g hg => ⟨(hl V g hg).choose, (hl V g hg).choose_spec, ha V g hg⟩⟩⟩

include hτ in
theorem ch_unique {U : Scheme.{0}} (y : Sec (T.X st) U) (c : Sec (K.X u) U) (a a' : Sec (L.X w) U)
    (ha : Ch τ μ' ν' st u w h U y c a) (ha' : Ch τ μ' ν' st u w h U y c a') : a = a' := by
  obtain ⟨S, hS, hl⟩ := hτ.1 U st y
  refine (sec_ext_glue R (L.X w) U).1 _ _ ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨x, hx⟩ := hl V g hg
  try dsimp only
  rw [ha V g x hx, ha' V g x hx]

theorem ch_res {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec (T.X st) U) (c : Sec (K.X u) U) (a : Sec (L.X w) U)
    (ha : Ch τ μ' ν' st u w h U y c a) :
    Ch τ μ' ν' st u w h V (Sec.res g y) (Sec.res g c) (Sec.res g a) := by
  intro W k x hx
  rw [res_res', res_res']
  exact ha W (k ≫ g) x (by rw [hx, res_res'])

include hτ in
theorem ch_base {U : Scheme.{0}} (x : Tens I J U st) (c : Sec (K.X u) U) :
    Ch τ μ' ν' st u w h U (τ.lift U st x) c (B μ' ν' st u w h U c x) := by
  intro V g x' hx'
  rw [B_nat]
  apply key hτ
  rw [← lift_nat, hx']

include hτ in
theorem ch_add_y {U : Scheme.{0}} (y y' : Sec (T.X st) U) (c : Sec (K.X u) U) (a a' : Sec (L.X w) U)
    (ha : Ch τ μ' ν' st u w h U y c a) (ha' : Ch τ μ' ν' st u w h U y' c a') :
    Ch τ μ' ν' st u w h U (y + y') c (a + a') := by
  obtain ⟨S1, hS1, hl1⟩ := hτ.1 U st y
  obtain ⟨S2, hS2, hl2⟩ := hτ.1 U st y'
  refine ch_loc hτ μ' ν' st u w h _ _ _ ⟨S1 ⊓ S2, Scheme.etaleTopology.intersection_covering hS1 hS2, fun V g hg => ?_⟩
  obtain ⟨x1, e1⟩ := hl1 V g hg.1
  obtain ⟨x2, e2⟩ := hl2 V g hg.2
  exact ⟨x1 + x2, by rw [map_add, e1, e2, res_add'], by rw [res_add', ha V g x1 e1, ha' V g x2 e2, map_add]⟩

include hτ in
theorem ch_smul_y {U : Scheme.{0}} (r : ULift.{1} R) (y : Sec (T.X st) U) (c : Sec (K.X u) U) (a : Sec (L.X w) U)
    (ha : Ch τ μ' ν' st u w h U y c a) :
    Ch τ μ' ν' st u w h U (r • y) c (r • a) := by
  obtain ⟨S1, hS1, hl1⟩ := hτ.1 U st y
  refine ch_loc hτ μ' ν' st u w h _ _ _ ⟨S1, hS1, fun V g hg => ?_⟩
  obtain ⟨x1, e1⟩ := hl1 V g hg
  exact ⟨r • x1, by rw [map_smul, e1, res_smul'], by rw [res_smul', ha V g x1 e1, map_smul]⟩

theorem ch_add_c {U : Scheme.{0}} (y : Sec (T.X st) U) (c c' : Sec (K.X u) U) (a a' : Sec (L.X w) U)
    (ha : Ch τ μ' ν' st u w h U y c a) (ha' : Ch τ μ' ν' st u w h U y c' a') :
    Ch τ μ' ν' st u w h U y (c + c') (a + a') := by
  intro V g x hx
  rw [res_add', ha V g x hx, ha' V g x hx, res_add', B_add_c]

theorem ch_smul_c {U : Scheme.{0}} (r : ULift.{1} R) (y : Sec (T.X st) U) (c : Sec (K.X u) U) (a : Sec (L.X w) U)
    (ha : Ch τ μ' ν' st u w h U y c a) :
    Ch τ μ' ν' st u w h U y (r • c) (r • a) := by
  intro V g x hx
  rw [res_smul', ha V g x hx, res_smul', B_smul_c]

end Glue

end TensAssoc
end GlobalTheory.EtC

namespace GlobalTheory.EtC
namespace TensAssoc

variable {R : Type} [CommRing R] {I J K T M L : Cx R}

theorem res_usmul {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (k : ℤˣ) (a : Sec F U) :
    Sec.res g (k • a) = k • Sec.res g a := by
  rw [Units.smul_def, Units.smul_def]
  exact map_zsmul _ _ _

section Build
variable {τ : Pair I J T} (hτ : τ.IsTensor) (μ' : Pair J K M) (ν' : Pair I M L)

noncomputable def nu (U : Scheme.{0}) (st u w : ℤ) (h : st + u = w) (y : Sec (T.X st) U) (c : Sec (K.X u) U) :
    Sec (L.X w) U :=
  (ch_exists hτ μ' ν' st u w h U y c).choose

theorem nu_spec (U : Scheme.{0}) (st u w : ℤ) (h : st + u = w) (y : Sec (T.X st) U) (c : Sec (K.X u) U) :
    Ch τ μ' ν' st u w h U y c (nu hτ μ' ν' U st u w h y c) :=
  (ch_exists hτ μ' ν' st u w h U y c).choose_spec

noncomputable def nuL (U : Scheme.{0}) (st u w : ℤ) (h : st + u = w) :
    Sec (T.X st) U →ₗ[ULift.{1} R] Sec (K.X u) U →ₗ[ULift.{1} R] Sec (L.X w) U :=
  LinearMap.mk₂ (ULift.{1} R) (nu hτ μ' ν' U st u w h)
    (fun y y' c => ch_unique hτ μ' ν' st u w h _ c _ _ (nu_spec hτ μ' ν' U st u w h _ c)
      (ch_add_y hτ μ' ν' st u w h y y' c _ _ (nu_spec hτ μ' ν' U st u w h y c) (nu_spec hτ μ' ν' U st u w h y' c)))
    (fun r y c => ch_unique hτ μ' ν' st u w h _ c _ _ (nu_spec hτ μ' ν' U st u w h _ c)
      (ch_smul_y hτ μ' ν' st u w h r y c _ (nu_spec hτ μ' ν' U st u w h y c)))
    (fun y c c' => ch_unique hτ μ' ν' st u w h y _ _ _ (nu_spec hτ μ' ν' U st u w h y _)
      (ch_add_c μ' ν' st u w h y c c' _ _ (nu_spec hτ μ' ν' U st u w h y c) (nu_spec hτ μ' ν' U st u w h y c')))
    (fun r y c => ch_unique hτ μ' ν' st u w h y _ _ _ (nu_spec hτ μ' ν' U st u w h y _)
      (ch_smul_c μ' ν' st u w h r y c _ (nu_spec hτ μ' ν' U st u w h y c)))

theorem nuL_apply (U : Scheme.{0}) (st u w : ℤ) (h : st + u = w) (y : Sec (T.X st) U) (c : Sec (K.X u) U) :
    nuL hτ μ' ν' U st u w h y c = nu hτ μ' ν' U st u w h y c := rfl

theorem nu_res {V U : Scheme.{0}} (g : V ⟶ U) (st u w : ℤ) (h : st + u = w) (y : Sec (T.X st) U) (c : Sec (K.X u) U) :
    Sec.res g (nuL hτ μ' ν' U st u w h y c) = nuL hτ μ' ν' V st u w h (Sec.res g y) (Sec.res g c) :=
  ch_unique hτ μ' ν' st u w h _ _ _ _ (ch_res μ' ν' st u w h g y c _ (nu_spec hτ μ' ν' U st u w h y c))
    (nu_spec hτ μ' ν' V st u w h _ _)

theorem main (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w) (h3 : t + u = tu)
    (h4 : s + tu = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U) (c : Sec (K.X u) U) :
    nuL hτ μ' ν' U st u w h2 (τ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c) := by
  subst h3
  have e : τ.mul U s t st h1 a b = τ.lift U st (DirectSum.lof (ULift.{1} R) _ (fun p : {p : ℤ × ℤ // p.1 + p.2 = st} =>
      Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(s, t), h1⟩ (a ⊗ₜ b)) :=
    (lift_lof τ U st ⟨(s, t), h1⟩ a b).symm
  rw [nuL_apply, e]
  exact (ch_unique hτ μ' ν' st u w h2 _ c _ _ (nu_spec hτ μ' ν' U st u w h2 _ c)
    (ch_base hτ μ' ν' st u w h2 _ c)).trans (B_lof μ' ν' st u w h2 U c ⟨(s, t), h1⟩ a b)

theorem leib_mul (U : Scheme.{0}) (st u w : ℤ) (h : st + u = w) (s t : ℤ) (hp : s + t = st)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) (c : Sec (K.X u) U) :
    Sec.map (L.d w (w + 1)) (nuL hτ μ' ν' U st u w h (τ.mul U s t st hp a b) c) =
      nuL hτ μ' ν' U (st + 1) u (w + 1) (by omega) (Sec.map (T.d st (st + 1)) (τ.mul U s t st hp a b)) c +
      st.negOnePow • nuL hτ μ' ν' U st (u + 1) (w + 1) (by omega) (τ.mul U s t st hp a b) (Sec.map (K.d u (u + 1)) c) := by
  rw [τ.leibniz]
  simp only [map_add, LinearMap.add_apply, Units.smul_def, map_zsmul, LinearMap.smul_apply]
  rw [main hτ μ' ν' U s t u st (t + u) w hp h rfl (by omega),
    main hτ μ' ν' U (s + 1) t u (st + 1) (t + u) (w + 1) (by omega) (by omega) rfl (by omega),
    main hτ μ' ν' U s (t + 1) u (st + 1) (t + u + 1) (w + 1) (by omega) (by omega) (by omega) (by omega),
    main hτ μ' ν' U s t (u + 1) st (t + u + 1) (w + 1) hp (by omega) (by omega) (by omega)]
  rw [ν'.leibniz, μ'.leibniz]
  simp only [map_add, Units.smul_def, map_zsmul, smul_add]
  subst hp
  rw [Int.negOnePow_add, Units.val_mul, mul_smul]
  abel

theorem leib_lift (U : Scheme.{0}) (st u w : ℤ) (h : st + u = w) (x : Tens I J U st) (c : Sec (K.X u) U) :
    Sec.map (L.d w (w + 1)) (nuL hτ μ' ν' U st u w h (τ.lift U st x) c) =
      nuL hτ μ' ν' U (st + 1) u (w + 1) (by omega) (Sec.map (T.d st (st + 1)) (τ.lift U st x)) c +
      st.negOnePow • nuL hτ μ' ν' U st (u + 1) (w + 1) (by omega) (τ.lift U st x) (Sec.map (K.d u (u + 1)) c) := by
  induction x using tens_ind with
  | h0 => simp
  | hadd x y hx hy =>
    simp only [map_add, LinearMap.add_apply, smul_add, hx, hy]
    abel
  | hof p a b =>
    rw [lift_lof]
    exact leib_mul hτ μ' ν' U st u w h p.1.1 p.1.2 p.2 a b c

theorem leib (U : Scheme.{0}) (st u w : ℤ) (h : st + u = w) (y : Sec (T.X st) U) (c : Sec (K.X u) U) :
    Sec.map (L.d w (w + 1)) (nuL hτ μ' ν' U st u w h y c) =
      nuL hτ μ' ν' U (st + 1) u (w + 1) (by omega) (Sec.map (T.d st (st + 1)) y) c +
      st.negOnePow • nuL hτ μ' ν' U st (u + 1) (w + 1) (by omega) y (Sec.map (K.d u (u + 1)) c) := by
  obtain ⟨S, hS, hl⟩ := hτ.1 U st y
  refine (sec_ext_glue R (L.X (w + 1)) U).1 _ _ ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨x, hx⟩ := hl V g hg
  try dsimp only
  rw [res_add', res_usmul, res_map', nu_res, nu_res, nu_res, res_map', res_map', ← hx]
  exact leib_lift hτ μ' ν' V st u w h x _

noncomputable def nuPair : Pair T K L where
  mul U s t w h := nuL hτ μ' ν' U s t w h
  nat g s t w h a b := nu_res hτ μ' ν' g s t w h a b
  leibniz U s t w h a b := leib hτ μ' ν' U s t w h a b

end Build
end TensAssoc

theorem tensor_assoc_desc : ∀ (R : Type) [CommRing R] {I J K T T3 : Cx R} (τ : Pair I J T) (τ' : Pair T K T3),
    τ.IsTensor → τ'.IsTensor → ∀ {M L : Cx R} (μ' : Pair J K M) (ν' : Pair I M L), ∃ ν : Pair T K L,
    ∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w) (h3 : t + u = tu) (h4 : s + tu = w) a b c,
    ν.mul U st u w h2 (τ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c) := by
  intro R _ I J K T T3 τ τ' hτ _ M L μ' ν'
  exact ⟨TensAssoc.nuPair hτ μ' ν', fun U s t u st tu w h1 h2 h3 h4 a b c =>
    TensAssoc.main hτ μ' ν' U s t u st tu w h1 h2 h3 h4 a b c⟩

end GlobalTheory.EtC
