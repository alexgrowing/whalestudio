import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCochainEvEqOfNaturalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexDifferentialValuesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKummerTorsorSplittingKummerTorsorSplittingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassTateTwistCocycleUniqueNaturalAddiStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf

noncomputable section

namespace UpperTheory.ChernClassOfTrivializedBundle

private theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  unfold Loc at h ⊢
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

private theorem loc_bind {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ (V : Scheme.{0}) (g : V ⟶ U), P V g → Loc V fun W k => Q W (k ≫ g)) : Loc U Q := by
  unfold Loc at h hPQ ⊢
  obtain ⟨S, hS, hP⟩ := h
  have hc : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → ∃ T ∈ Scheme.etaleTopology V,
      ∀ (W : Scheme.{0}) (k : W ⟶ V), T.arrows k → Q W (k ≫ g) := fun V g hg => hPQ V g (hP V g hg)
  choose T hT hTQ using hc
  refine ⟨Sieve.bind S.arrows (fun V g hg => T V g hg), Scheme.etaleTopology.bind_covering hS (fun V g hg => hT V g hg), ?_⟩
  rintro W _ ⟨V, k, g, hg, hk, rfl⟩
  exact hTQ V g hg W k hk

section Res
variable {R : Type} [CommRing R] {F G : Shv R}

private theorem res_comp {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res (k ≫ g) a = Sec.res k (Sec.res g a) := by
  simp [Sec.res]

private theorem res_id {U : Scheme.{0}} (a : Sec F U) : Sec.res (𝟙 U) a = a := by
  simp [Sec.res]

private theorem map_res (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.map φ (Sec.res g a) = Sec.res g (Sec.map φ a) := by
  exact congrArg (fun f => ModuleCat.Hom.hom f a) (φ.hom.naturality g.op)

private theorem res_add {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec F U) :
    Sec.res g (a + b) = Sec.res g a + Sec.res g b := map_add (F.obj.map g.op).hom a b

private theorem res_sub {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec F U) :
    Sec.res g (a - b) = Sec.res g a - Sec.res g b := map_sub (F.obj.map g.op).hom a b

private theorem res_zero {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec F U) = 0 := map_zero (F.obj.map g.op).hom

private theorem smap_add (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a + b) = Sec.map φ a + Sec.map φ b := map_add (φ.hom.app (op U)).hom a b

private theorem smap_sub (φ : F ⟶ G) {U : Scheme.{0}} (a b : Sec F U) :
    Sec.map φ (a - b) = Sec.map φ a - Sec.map φ b := map_sub (φ.hom.app (op U)).hom a b

private theorem smap_neg (φ : F ⟶ G) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map φ (-a) = - Sec.map φ a := map_neg (φ.hom.app (op U)).hom a

private theorem smap_nsmul (φ : F ⟶ G) {U : Scheme.{0}} (n : ℕ) (a : Sec F U) :
    Sec.map φ (n • a) = n • Sec.map φ a := map_nsmul (φ.hom.app (op U)).hom n a

private theorem sep {U : Scheme.{0}} {a b : Sec F U} (h : Loc U fun _ g => Sec.res g a = Sec.res g b) : a = b :=
  (GlobalTheory.T.etaleSheafSections_ext_and_glue R F U).1 a b h

private theorem glue {U : Scheme.{0}} (P : ∀ (V : Scheme.{0}) (_ : V ⟶ U), Sec F V → Prop)
    (hex : Loc U fun V g => ∃ a, P V g a)
    (hres : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) a, P V g a → P W (k ≫ g) (Sec.res k a))
    (huniq : ∀ (V : Scheme.{0}) (g : V ⟶ U) a b, P V g a → P V g b → a = b) :
    ∃ a : Sec F U, ∀ (V : Scheme.{0}) (g : V ⟶ U) b, P V g b → Sec.res g a = b := by
  unfold Loc at hex
  obtain ⟨S, hS, hP⟩ := hex
  choose s hs using hP
  obtain ⟨a, ha⟩ := (GlobalTheory.T.etaleSheafSections_ext_and_glue R F U).2 S hS s
    (fun V W g k hg => huniq W (k ≫ g) _ _ (hres V W g k _ (hs V g hg)) (hs W (k ≫ g) _))
  refine ⟨a, fun V g b hb => sep ?_⟩
  unfold Loc
  refine ⟨S.pullback g, (Scheme.etaleTopology).pullback_stable g hS, fun W k hk => ?_⟩
  show Sec.res k (Sec.res g a) = Sec.res k b
  rw [← res_comp, ha W (k ≫ g) hk]
  exact huniq W (k ≫ g) _ _ (hs W (k ≫ g) hk) (hres V W g k b hb)

end Res

private abbrev II (q : ℕ) : Cx (ZMod q) := res (ZMod q) (tw q 1)

private abbrev dd (q : ℕ) {U : Scheme.{0}} (a : Sec ((II q).X 0) U) : Sec ((II q).X 1) U := Sec.map ((II q).d 0 1) a

private abbrev ur {V U : Scheme.{0}} (g : V ⟶ U) : (Γ(U, ⊤))ˣ →* (Γ(V, ⊤))ˣ := Units.map g.appTop.hom.toMonoidHom

private theorem ur_id {U : Scheme.{0}} (u : (Γ(U, ⊤))ˣ) : ur (𝟙 U) u = u := by
  ext; simp

private theorem ur_comp {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    ur (k ≫ g) u = ur k (ur g u) := by
  ext
  simp [ur]
  rfl

variable {q : ℕ} [NeZero q]

private theorem unit_res {V U : Scheme.{0}} (g : V ⟶ U) (hq : IsUnit (q : Γ(U, ⊤))) : IsUnit (q : Γ(V, ⊤)) := by
  simpa using hq.map g.appTop.hom

private theorem K_nat {V U : Scheme.{0}} (g : V ⟶ U) (hq : IsUnit (q : Γ(U, ⊤))) (v : (Γ(U, ⊤))ˣ) :
    Sec.res g (kumT q U v) = kumT q V (ur g v) := (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).1 V U g v hq

private theorem prim_pow {A : Type} [CommRing A] (ζ : Prim q A) : ζ.1 ^ q = 1 := by
  obtain ⟨p, hp⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hp
  rw [map_mul, ζ.2.2, zero_mul, map_sub, map_pow, Polynomial.aeval_X, map_one] at h
  exact sub_eq_zero.mp h

private theorem K_pow {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (Z : (Γ(U, ⊤))ˣ) (hZ : (Z : Γ(U, ⊤)) = ζ.1) (n : ℕ)
    (v : (Γ(U, ⊤))ˣ) : kumT q U (Z ^ n * v) = kumT q U v + n • resGen 1 ζ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).2 U ζ (Z ^ n * v) (Z ^ (n + 1) * v) (by
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, hZ]
      ring)
    rw [h, ih, succ_nsmul, add_assoc]

private theorem tau_loc {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤))) (u : (Γ(U, ⊤))ˣ) (hu : u ^ q = 1) :
    Loc U fun V g => ∃ τ : Sec ((II q).X 0) V, dd q τ = 0 ∧ ∀ v, kumT q V (ur g u * v) = kumT q V v + τ := by
  refine loc_bind ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).1 hq) fun V g hζ => ?_
  obtain ⟨ζ⟩ := hζ
  have hu' : (↑(ur g u) : Γ(V, ⊤)) ^ q = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hu, map_one, Units.val_one]
  refine loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).2.2.1 ζ _ hu') fun W k ha => ?_
  obtain ⟨a, ha⟩ := ha
  have hz : (Prim.map k.appTop.hom ζ).1 ^ q = 1 := prim_pow _
  have hZ : ur (k ≫ g) u = Units.ofPowEqOne _ q hz (NeZero.ne q) ^ a := by
    ext
    rw [ur_comp, Units.val_pow_eq_pow_val, Units.val_ofPowEqOne]
    exact ha
  refine ⟨a • resGen 1 (Prim.map k.appTop.hom ζ), ?_, fun v => ?_⟩
  · have hr : Sec.map ((II q).d 0 1) (resGen 1 (Prim.map k.appTop.hom ζ)) = 0 :=
      ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness (ZMod q) (tw q 1) W).1 _).mpr ⟨_, rfl⟩
    show Sec.map ((II q).d 0 1) (a • resGen 1 (Prim.map k.appTop.hom ζ)) = 0
    rw [smap_nsmul, hr, smul_zero]
  · rw [hZ]
    exact K_pow _ _ (Units.val_ofPowEqOne _ _ _ _) a v

private theorem kumT_ur_comp_mul_eq_add_res {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤))) (u : (Γ(U, ⊤))ˣ) (hu : u ^ q = 1)
    {V : Scheme.{0}} (g : V ⟶ U) (τ : Sec ((II q).X 0) V) (hτ : ∀ v, kumT q V (ur g u * v) = kumT q V v + τ)
    {W : Scheme.{0}} (k : W ⟶ V) (v : (Γ(W, ⊤))ˣ) :
    kumT q W (ur (k ≫ g) u * v) = kumT q W v + Sec.res k τ := by
  have hV := unit_res g hq
  have hW := unit_res (k ≫ g) hq
  have hu' : ur (k ≫ g) u ^ q = 1 := by rw [← map_pow, hu, map_one]
  apply sep
  refine loc_mono (tau_loc hW _ hu') fun W' k' hP => ?_
  obtain ⟨τ', _, h'⟩ := hP
  show Sec.res k' _ = Sec.res k' _
  have e1 : kumT q W' (ur k' (ur k (ur g u))) = kumT q W' 1 + τ' := by
    have := h' 1
    simpa only [ur_comp, mul_one] using this
  have e2 : kumT q W' (ur k' (ur k (ur g u))) = kumT q W' 1 + Sec.res (k' ≫ k) τ := by
    have := congrArg (Sec.res (k' ≫ k)) (hτ 1)
    rw [mul_one, K_nat _ hV, res_add, K_nat _ hV, map_one, ur_comp] at this
    exact this
  have e3 : τ' = Sec.res (k' ≫ k) τ := add_left_cancel (e1.symm.trans e2)
  rw [K_nat _ hW, res_add, K_nat _ hW, map_mul, ← res_comp, ← e3]
  have := h' (ur k' v)
  simp only [ur_comp] at this ⊢
  exact this

private theorem tau_exists {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤))) (u : (Γ(U, ⊤))ˣ) (hu : u ^ q = 1) :
    ∃ τ : Sec ((II q).X 0) U, dd q τ = 0 ∧ ∀ v, kumT q U (u * v) = kumT q U v + τ := by
  obtain ⟨a, ha⟩ := glue (F := (II q).X 0)
    (fun V g τ => dd q τ = 0 ∧ ∀ v, kumT q V (ur g u * v) = kumT q V v + τ)
    (tau_loc hq u hu)
    (fun V W g k τ hP => ⟨by
        show Sec.map _ (Sec.res k τ) = 0
        rw [map_res]
        exact (congrArg (Sec.res k) hP.1).trans (res_zero k), kumT_ur_comp_mul_eq_add_res hq u hu g τ hP.2 k⟩)
    (fun V g a b ha hb => add_left_cancel ((ha.2 1).symm.trans (hb.2 1)))
  have hloc := tau_loc hq u hu
  refine ⟨a, sep ?_, fun v => sep ?_⟩
  · refine loc_mono hloc fun V g hP => ?_
    show Sec.res g (Sec.map _ a) = Sec.res g 0
    rw [← map_res, ha V g _ hP.choose_spec, res_zero]
    exact hP.choose_spec.1
  · refine loc_mono hloc fun V g hP => ?_
    show Sec.res g _ = Sec.res g _
    rw [K_nat g hq, map_mul, hP.choose_spec.2, res_add, K_nat g hq, ha V g _ hP.choose_spec]

private theorem root_ratio {A : Type} [CommGroup A] {a a' : A} (h : a ^ q = a' ^ q) : (a' * a⁻¹) ^ q = 1 := by
  rw [mul_pow, inv_pow, ← h, mul_inv_cancel]

private theorem dK_eq {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤))) {a a' : (Γ(U, ⊤))ˣ} (h : a ^ q = a' ^ q) :
    dd q (kumT q U a) = dd q (kumT q U a') := by
  obtain ⟨τ, hτ0, hτ⟩ := tau_exists hq (a' * a⁻¹) (root_ratio h)
  have h0 : Sec.map ((II q).d 0 1) τ = 0 := hτ0
  have hA : kumT q U a' = kumT q U a + τ := by rw [← hτ a, inv_mul_cancel_right]
  show Sec.map ((II q).d 0 1) (kumT q U a) = Sec.map ((II q).d 0 1) (kumT q U a')
  rw [hA, smap_add, h0, add_zero]

private abbrev ff (q : ℕ) {U : Scheme.{0}} (a b : (Γ(U, ⊤))ˣ) : Sec ((II q).X 0) U :=
  kumT q U a + kumT q U b - kumT q U (a * b)

private theorem ff_eq {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤))) {a a' b b' : (Γ(U, ⊤))ˣ} (ha : a ^ q = a' ^ q)
    (hb : b ^ q = b' ^ q) : ff q a b = ff q a' b' := by
  obtain ⟨τ, -, hτ⟩ := tau_exists hq (a' * a⁻¹) (root_ratio ha)
  obtain ⟨σ, -, hσ⟩ := tau_exists hq (b' * b⁻¹) (root_ratio hb)
  have e : a' * b' = a' * a⁻¹ * (b' * b⁻¹ * (a * b)) := by
    rw [show a' * a⁻¹ * (b' * b⁻¹ * (a * b)) = a' * b' * (a⁻¹ * a) * (b⁻¹ * b) by ac_rfl,
      inv_mul_cancel, inv_mul_cancel, mul_one, mul_one]
  have hA : kumT q U a' = kumT q U a + τ := by rw [← hτ a, inv_mul_cancel_right]
  have hB : kumT q U b' = kumT q U b + σ := by rw [← hσ b, inv_mul_cancel_right]
  have hAB : kumT q U (a' * b') = kumT q U (a * b) + σ + τ := by rw [e, hτ, hσ]
  show kumT q U a + kumT q U b - kumT q U (a * b) = kumT q U a' + kumT q U b' - kumT q U (a' * b')
  rw [hA, hB, hAB]
  abel

private theorem ff_nat {V U : Scheme.{0}} (g : V ⟶ U) (hq : IsUnit (q : Γ(U, ⊤))) (a b : (Γ(U, ⊤))ˣ) :
    Sec.res g (ff q a b) = ff q (ur g a) (ur g b) := by
  show Sec.res g (kumT q U a + kumT q U b - kumT q U (a * b)) =
    kumT q V (ur g a) + kumT q V (ur g b) - kumT q V (ur g a * ur g b)
  rw [res_sub, res_add, K_nat g hq, K_nat g hq, K_nat g hq, map_mul]

private theorem roots {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤))) (s : (Γ(U, ⊤))ˣ) :
    Loc U fun V g => ∃ a : (Γ(V, ⊤))ˣ, a ^ q = ur g s := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).2.2.2 hq s

private theorem roots2 {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤))) (s t : (Γ(U, ⊤))ˣ) :
    Loc U fun V g => ∃ a b : (Γ(V, ⊤))ˣ, a ^ q = ur g s ∧ b ^ q = ur g t := by
  refine loc_bind (roots hq s) fun V g ⟨a, ha⟩ => loc_mono (roots (unit_res g hq) (ur g t)) fun W k ⟨b, hb⟩ => ?_
  exact ⟨ur k a, b, by rw [← map_pow, ha, ur_comp], by rw [hb, ur_comp]⟩

private theorem roots3 {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤))) (s t r : (Γ(U, ⊤))ˣ) :
    Loc U fun V g => ∃ a b c : (Γ(V, ⊤))ˣ, a ^ q = ur g s ∧ b ^ q = ur g t ∧ c ^ q = ur g r := by
  refine loc_bind (roots2 hq s t) fun V g ⟨a, b, ha, hb⟩ => loc_mono (roots (unit_res g hq) (ur g r)) fun W k ⟨c, hc⟩ => ?_
  exact ⟨ur k a, ur k b, c, by rw [← map_pow, ha, ur_comp], by rw [← map_pow, hb, ur_comp], by rw [hc, ur_comp]⟩

private def Dd (q : ℕ) [NeZero q] {U : Scheme.{0}} (s : (Γ(U, ⊤))ˣ) : Sec ((II q).X 1) U :=
  pick fun D => ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ q = ur g s → Sec.res g D = dd q (kumT q V v)

private theorem Dd_spec {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤))) (s : (Γ(U, ⊤))ˣ) (V : Scheme.{0}) (g : V ⟶ U)
    (v : (Γ(V, ⊤))ˣ) (hv : v ^ q = ur g s) : Sec.res g (Dd q s) = dd q (kumT q V v) := by
  have hP : ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ q = ur g s →
      ∀ (W : Scheme.{0}) (k : W ⟶ V) (w : (Γ(W, ⊤))ˣ), w ^ q = ur (k ≫ g) s →
        Sec.res k (dd q (kumT q V v)) = dd q (kumT q W w) := by
    intro V g v hv W k w hw
    show Sec.res k (Sec.map _ _) = _
    rw [← map_res, K_nat k (unit_res g hq)]
    exact dK_eq (unit_res (k ≫ g) hq) (by rw [← map_pow, hv, hw, ur_comp])
  obtain ⟨D, hD⟩ := glue (F := (II q).X 1)
    (fun V g D => ∀ (W : Scheme.{0}) (k : W ⟶ V) (w : (Γ(W, ⊤))ˣ), w ^ q = ur (k ≫ g) s →
      Sec.res k D = dd q (kumT q W w))
    (loc_mono (roots hq s) fun V g ⟨v, hv⟩ => ⟨_, hP V g v hv⟩)
    (fun V W g k D hD W' k' w hw => by
      rw [← res_comp]
      exact hD W' (k' ≫ k) w (by rw [hw, Category.assoc]))
    (fun V g D D' hD hD' => sep (loc_mono (roots (unit_res g hq) (ur g s)) fun W k ⟨w, hw⟩ =>
      (hD W k w (by rw [hw, ur_comp])).trans (hD' W k w (by rw [hw, ur_comp])).symm))
  have hex : ∃ D, ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ q = ur g s →
      Sec.res g D = dd q (kumT q V v) :=
    ⟨D, fun V g v hv => hD V g _ (hP V g v hv)⟩
  exact (pick_spec hex) V g v hv

private theorem Dd_root {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤))) {s v : (Γ(U, ⊤))ˣ} (hv : v ^ q = s) :
    Dd q s = dd q (kumT q U v) := by
  have := Dd_spec hq s U (𝟙 U) v (by rw [hv, ur_id])
  rwa [res_id] at this

private theorem Dd_nat {V U : Scheme.{0}} (g : V ⟶ U) (hq : IsUnit (q : Γ(U, ⊤))) (s : (Γ(U, ⊤))ˣ) :
    Sec.res g (Dd q s) = Dd q (ur g s) := by
  apply sep
  refine loc_mono (roots (unit_res g hq) (ur g s)) fun W k hw => ?_
  obtain ⟨w, hw⟩ := hw
  show Sec.res k (Sec.res g (Dd q s)) = Sec.res k (Dd q (ur g s))
  rw [← res_comp, Dd_spec hq s W (k ≫ g) w (by rw [hw, ur_comp]), Dd_spec (unit_res g hq) (ur g s) W k w hw]

private theorem dd_dd {U : Scheme.{0}} (a : Sec ((II q).X 0) U) : Sec.map ((II q).d 1 2) (dd q a) = 0 := by
  show (((II q).d 0 1 ≫ (II q).d 1 2).hom.app (op U)).hom a = 0
  rw [HomologicalComplex.d_comp_d]
  rfl

private theorem Dd_closed {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤))) (s : (Γ(U, ⊤))ˣ) :
    Sec.map ((II q).d 1 2) (Dd q s) = 0 := by
  apply sep
  refine loc_mono (roots hq s) fun V g hv => ?_
  obtain ⟨v, hv⟩ := hv
  show Sec.res g (Sec.map _ (Dd q s)) = Sec.res g 0
  rw [← map_res, res_zero, Dd_spec hq s V g v hv]
  exact dd_dd _

private def Ph (q : ℕ) [NeZero q] {U : Scheme.{0}} (s t : (Γ(U, ⊤))ˣ) : Sec ((II q).X 0) U :=
  pick fun D => ∀ (V : Scheme.{0}) (g : V ⟶ U) (a b : (Γ(V, ⊤))ˣ), a ^ q = ur g s → b ^ q = ur g t →
    Sec.res g D = ff q a b

private theorem Ph_spec {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤))) (s t : (Γ(U, ⊤))ˣ) (V : Scheme.{0}) (g : V ⟶ U)
    (a b : (Γ(V, ⊤))ˣ) (ha : a ^ q = ur g s) (hb : b ^ q = ur g t) : Sec.res g (Ph q s t) = ff q a b := by
  have hP : ∀ (V : Scheme.{0}) (g : V ⟶ U) (a b : (Γ(V, ⊤))ˣ), a ^ q = ur g s → b ^ q = ur g t →
      ∀ (W : Scheme.{0}) (k : W ⟶ V) (a' b' : (Γ(W, ⊤))ˣ), a' ^ q = ur (k ≫ g) s → b' ^ q = ur (k ≫ g) t →
        Sec.res k (ff q a b) = ff q a' b' := by
    intro V g a b ha hb W k a' b' ha' hb'
    rw [ff_nat k (unit_res g hq)]
    exact ff_eq (unit_res (k ≫ g) hq) (by rw [← map_pow, ha, ha', ur_comp]) (by rw [← map_pow, hb, hb', ur_comp])
  obtain ⟨D, hD⟩ := glue (F := (II q).X 0)
    (fun V g D => ∀ (W : Scheme.{0}) (k : W ⟶ V) (a' b' : (Γ(W, ⊤))ˣ), a' ^ q = ur (k ≫ g) s →
      b' ^ q = ur (k ≫ g) t → Sec.res k D = ff q a' b')
    (loc_mono (roots2 hq s t) fun V g ⟨a, b, ha, hb⟩ => ⟨_, hP V g a b ha hb⟩)
    (fun V W g k D hD W' k' a' b' ha' hb' => by
      rw [← res_comp]
      exact hD W' (k' ≫ k) a' b' (by rw [ha', Category.assoc]) (by rw [hb', Category.assoc]))
    (fun V g D D' hD hD' => sep (loc_mono (roots2 (unit_res g hq) (ur g s) (ur g t)) fun W k ⟨a', b', ha', hb'⟩ =>
      (hD W k a' b' (by rw [ha', ur_comp]) (by rw [hb', ur_comp])).trans
        (hD' W k a' b' (by rw [ha', ur_comp]) (by rw [hb', ur_comp])).symm))
  have hex : ∃ D, ∀ (V : Scheme.{0}) (g : V ⟶ U) (a b : (Γ(V, ⊤))ˣ), a ^ q = ur g s → b ^ q = ur g t →
      Sec.res g D = ff q a b :=
    ⟨D, fun V g a b ha hb => hD V g _ (hP V g a b ha hb)⟩
  exact (pick_spec hex) V g a b ha hb

private theorem Ph_root {U : Scheme.{0}} (hq : IsUnit (q : Γ(U, ⊤))) {s t a b : (Γ(U, ⊤))ˣ} (ha : a ^ q = s)
    (hb : b ^ q = t) : Ph q s t = ff q a b := by
  have := Ph_spec hq s t U (𝟙 U) a b (by rw [ha, ur_id]) (by rw [hb, ur_id])
  rwa [res_id] at this

private theorem Ph_nat {V U : Scheme.{0}} (g : V ⟶ U) (hq : IsUnit (q : Γ(U, ⊤))) (s t : (Γ(U, ⊤))ˣ) :
    Sec.res g (Ph q s t) = Ph q (ur g s) (ur g t) := by
  apply sep
  refine loc_mono (roots2 (unit_res g hq) (ur g s) (ur g t)) fun W k hw => ?_
  obtain ⟨a, b, ha, hb⟩ := hw
  show Sec.res k (Sec.res g (Ph q s t)) = Sec.res k (Ph q (ur g s) (ur g t))
  rw [← res_comp, Ph_spec hq s t W (k ≫ g) a b (by rw [ha, ur_comp]) (by rw [hb, ur_comp]),
    Ph_spec (unit_res g hq) (ur g s) (ur g t) W k a b ha hb]

section Line
variable {X : Spc} (L : X ⟶ ofCat (glCat 1))

private theorem face_res {p : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx X (p + 1) U) (i : Fin (p + 2)) :
    (x.res g).face i = (x.face i).res g := NatTrans.naturality_apply (SimplicialObject.δ X i) g.op x

private theorem face_face {p : ℕ} {U : Scheme.{0}} (x : Sx X (p + 2) U) (i i' : Fin (p + 2)) (j j' : Fin (p + 3))
    (h : SimplexCategory.δ i ≫ SimplexCategory.δ j = SimplexCategory.δ i' ≫ SimplexCategory.δ j') :
    (x.face j).face i = (x.face j').face i' := by
  have e : SimplicialObject.δ X j ≫ SimplicialObject.δ X i = SimplicialObject.δ X j' ≫ SimplicialObject.δ X i' := by
    simp only [SimplicialObject.δ, ← X.map_comp, ← op_comp, h]
  exact ConcreteCategory.congr_hom (congr_app e (op U)) x

private theorem sub0 {U : Scheme.{0}} (x : Sx X 2 U) : x.sub 0 1 (by omega) = x.face 2 := by
  have e : SimplexCategory.subinterval (n := 2) 0 1 (by omega) = SimplexCategory.δ (n := 1) 2 := by
    ext i; fin_cases i <;> rfl
  simp only [Sx.sub, Sx.face, SimplicialObject.δ, e]

private theorem sub1 {U : Scheme.{0}} (x : Sx X 2 U) : x.sub 1 1 (by omega) = x.face 0 := by
  have e : SimplexCategory.subinterval (n := 2) 1 1 (by omega) = SimplexCategory.δ (n := 1) 0 := by
    ext i; fin_cases i <;> rfl
  simp only [Sx.sub, Sx.face, SimplicialObject.δ, e]

private theorem glDet_map {A B : CommRingCat.{0}} (f : A ⟶ B) (m : GL (Fin 1) A) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f.hom m) =
      Units.map f.hom.toMonoidHom (Matrix.GeneralLinearGroup.det m) := by
  ext
  simp [Matrix.GeneralLinearGroup.det, RingHom.map_det]

private theorem lineUnit_res {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx X 1 U) :
    lineUnit L (x.res g) = ur g (lineUnit L x) := by
  have hn := NatTrans.naturality_apply (L.app (op (SimplexCategory.mk 1))) g.op x
  unfold lineUnit Sx.res
  rw [hn]
  have hm : ∀ y : Sx (ofCat (glCat 1)) 1 U, glMat (ConcreteCategory.hom (((ofCat (glCat 1)).obj (op (SimplexCategory.mk 1))).map g.op) y) =
      Matrix.GeneralLinearGroup.map g.appTop.hom (glMat y) := fun y => rfl
  rw [hm, glDet_map]

private theorem glMat_face {U : Scheme.{0}} (y : Sx (ofCat (glCat 1)) 2 U) :
    glMat (y.face 1) = glMat (y.face 0) * glMat (y.face 2) := by
  have e := ComposableArrows.map'_comp (C := SingleObj (GL (Fin 1) Γ(U, ⊤))) y 0 1 2
  exact e.trans (SingleObj.comp_as_mul _ _ _)

private theorem line_face {U : Scheme.{0}} (x : Sx X 2 U) :
    lineUnit L (x.face 1) = lineUnit L (x.face 2) * lineUnit L (x.face 0) := by
  have hf : ∀ i : Fin 3, ConcreteCategory.hom ((L.app (op (SimplexCategory.mk 1))).app (op U)) (x.face i) =
      Sx.face (E := ofCat (glCat 1)) (ConcreteCategory.hom ((L.app (op (SimplexCategory.mk 2))).app (op U)) x) i :=
    fun i => ConcreteCategory.congr_hom (congr_app (L.naturality (SimplexCategory.δ i).op) (op U)) x
  unfold lineUnit
  rw [hf, hf, hf, glMat_face, map_mul, mul_comm]

end Line

section Main
variable {X : Spc}

private def fam (A0 : ∀ U : Scheme.{0}, Sx X 0 U → Sec ((II q).X 1) U) (A1 : ∀ U : Scheme.{0}, Sx X 1 U → Sec ((II q).X 0) U) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 1 = s → ∀ U : Scheme.{0}, Sx X p U → Sec ((II q).X s) U
  | 0, s, h, U, x => Eq.rec (motive := fun s _ => Sec ((II q).X s) U) (A0 U x) (show (1 : ℤ) = s by simpa using h)
  | 1, s, h, U, x => Eq.rec (motive := fun s _ => Sec ((II q).X s) U) (A1 U x) (show (0 : ℤ) = s by simpa using h)
  | _ + 2, _, _, _, _ => 0

private theorem fam_nat (A0 : ∀ U : Scheme.{0}, Sx X 0 U → Sec ((II q).X 1) U)
    (A1 : ∀ U : Scheme.{0}, Sx X 1 U → Sec ((II q).X 0) U)
    (h0 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx X 0 U), Sec.res g (A0 U x) = A0 V (x.res g))
    (h1 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx X 1 U), Sec.res g (A1 U x) = A1 V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + 1 = s) (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx X p U) :
    Sec.res g (fam A0 A1 p s h U x) = fam A0 A1 p s h V (x.res g) := by
  rcases p with _ | _ | p
  · obtain rfl : s = 1 := by omega
    exact h0 V U g x
  · obtain rfl : s = 0 := by omega
    exact h1 V U g x
  · exact res_zero g

private theorem res_neg' {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.res g (-a) = - Sec.res g a := map_neg (F.obj.map g.op).hom a

private theorem main (L : X ⟶ ofCat (glCat 1)) (w : ∀ T : Scheme.{0}, Sx X 0 T → (Γ(T, ⊤))ˣ) (hI : Inv q X)
    (hT : IsTrivBy L w) : c1 q L = 0 := by
  obtain ⟨hwn, hwc⟩ := hT
  obtain ⟨γ, hγ, h0, h1, h2⟩ := (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).1 L hI
  rw [← hγ, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff γ 1 (by norm_num)]
  let A0 : ∀ U : Scheme.{0}, Sx X 0 U → Sec ((II q).X 1) U := fun U x => -Dd q (w U x)
  let A1 : ∀ U : Scheme.{0}, Sx X 1 U → Sec ((II q).X 0) U := fun U x => Ph q (lineUnit L x) (w U (x.face 0))
  have hA0 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx X 0 U), Sec.res g (A0 U x) = A0 V (x.res g) := by
    intro V U g x
    show Sec.res g (-Dd q (w U x)) = -Dd q (w V (x.res g))
    rw [res_neg', Dd_nat g (hI U ⟨x⟩), hwn]
  have hA1 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx X 1 U), Sec.res g (A1 U x) = A1 V (x.res g) := by
    intro V U g x
    show Sec.res g (Ph q (lineUnit L x) (w U (x.face 0))) = Ph q (lineUnit L (x.res g)) (w V ((x.res g).face 0))
    rw [Ph_nat g (hI U ⟨x.face 0⟩), lineUnit_res, face_res, hwn]
  obtain ⟨β, hβ⟩ := GlobalTheory.T.exists_cochain_ev_eq_of_natural' (ZMod q) (I := II q) (n := 1) (fam A0 A1) (fam_nat A0 A1 hA0 hA1)
  have hf0 : ∀ (U : Scheme.{0}) (x : Sx X 0 U) (h : -((0 : ℕ) : ℤ) + 1 = 1), fam A0 A1 0 1 h U x = A0 U x :=
    fun _ _ _ => rfl
  have hf1 : ∀ (U : Scheme.{0}) (x : Sx X 1 U) (h : -((1 : ℕ) : ℤ) + 1 = 0), fam A0 A1 1 0 h U x = A1 U x :=
    fun _ _ _ => rfl
  have hf2 : ∀ (U : Scheme.{0}) (x : Sx X 2 U) (h : -((2 : ℕ) : ℤ) + 1 = -1), fam A0 A1 2 (-1) h U x = 0 :=
    fun _ _ _ => rfl
  have hnat := (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q) (E := X) (I := II q) (n := 2)).2.1
  have hd := GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (I := II q) (show (1 : ℤ) + 1 = 2 by norm_num) β
  have hsign : (2 : ℤ).negOnePow = 1 := by decide
  refine ⟨β, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q) (E := X) (I := II q) (n := 2)).2.2.1 _ _ fun p s h U x => ?_⟩
  rcases p with _ | _ | _ | p
  · obtain rfl : s = 2 := by omega
    rw [(hd U).1 x, h0 U x, hβ, hf0]
    show Sec.map _ (-Dd q (w U x)) = 0
    rw [smap_neg, Dd_closed (hI U ⟨x⟩), neg_zero]
  · obtain rfl : s = 1 := by omega
    have hU := hI U ⟨x.face 0⟩
    apply sep
    refine loc_mono (roots2 hU (lineUnit L x) (w U (x.face 0))) fun V g hr => ?_
    obtain ⟨v, a, hv, ha⟩ := hr
    show Sec.res g _ = Sec.res g _
    rw [hnat, hnat]
    have hV := unit_res g hU
    have hv' : v ^ q = lineUnit L (x.res g) := by rw [lineUnit_res, hv]
    have ha' : a ^ q = w V ((x.res g).face 0) := by rw [face_res, hwn, ha]
    have hb' : (v * a) ^ q = w V ((x.res g).face 1) := by rw [← hwc, mul_pow, hv', ha']
    rw [(hd V).2 0 0 1 (by omega) (by omega) (x.res g), h1 V (x.res g) v hv', hsign, one_smul, Fin.sum_univ_two]
    simp only [hβ, zero_add, hf0, hf1, A0, A1, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
    rw [Ph_root hV hv' ha', Dd_root hV ha', Dd_root hV hb']
    simp only [ff, smap_add, smap_sub, smap_neg]
    abel
  · obtain rfl : s = 0 := by omega
    have hU := hI U ⟨(x.face 0).face 0⟩
    apply sep
    refine loc_mono (roots3 hU (lineUnit L (x.face 2)) (lineUnit L (x.face 0)) (w U ((x.face 0).face 0)))
      fun V g hr => ?_
    obtain ⟨α, b, c, hα, hb, hc⟩ := hr
    show Sec.res g _ = Sec.res g _
    rw [hnat, hnat]
    have hV := unit_res g hU
    have hα' : α ^ q = lineUnit L ((x.res g).face 2) := by rw [face_res, lineUnit_res, hα]
    have hb' : b ^ q = lineUnit L ((x.res g).face 0) := by rw [face_res, lineUnit_res, hb]
    have hc' : c ^ q = w V (((x.res g).face 0).face 0) := by rw [face_res, face_res, hwn, hc]
    have e1 : ((x.res g).face 1).face 0 = ((x.res g).face 0).face 0 :=
      face_face _ 0 0 1 0 (by ext i; fin_cases i; rfl)
    have e2 : ((x.res g).face 2).face 0 = ((x.res g).face 0).face 1 :=
      face_face _ 0 1 2 0 (by ext i; fin_cases i; rfl)
    have hαb : (α * b) ^ q = lineUnit L ((x.res g).face 1) := by rw [line_face, mul_pow, hα', hb']
    have hbc : (b * c) ^ q = w V (((x.res g).face 2).face 0) := by rw [e2, ← hwc, mul_pow, hb', hc']
    have hc1 : c ^ q = w V (((x.res g).face 1).face 0) := by rw [e1, hc']
    have hz : ∀ (φ : (II q).X (-1) ⟶ (II q).X 0), Sec.map φ (0 : Sec _ V) = 0 :=
      fun φ => map_zero (φ.hom.app (op V)).hom
    rw [(hd V).2 1 (-1) 0 (by omega) (by omega) (x.res g), h2 V (x.res g) α b (by rw [sub0, hα'])
      (by rw [sub1, hb']), hsign, one_smul, Fin.sum_univ_three]
    simp only [hβ, hf1, hf2, hz, A1, zero_add, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one,
      neg_one_sq, one_smul, neg_smul]
    rw [Ph_root hV hb' hc', Ph_root hV hαb hc1, Ph_root hV hα' hbc]
    simp only [ff, mul_assoc]
    abel
  · exact @Subsingleton.elim _ ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness (ZMod q) (tw q 1) U).2.2.2 s (by omega)) _ _

end Main

end UpperTheory.ChernClassOfTrivializedBundle

end

theorem UpperTheory.firstChernClass_eq_zero_of_isTrivialized :
    ∀ (q : ℕ) [NeZero q] {X : Spc} (L : X ⟶ ofCat (glCat 1)) (w : ∀ T : Scheme.{0}, Sx X 0 T → (Γ(T, ⊤))ˣ), Inv q X → IsTrivBy L w → c1 q L = 0 := by
  intro q _ X L w hI hT
  exact UpperTheory.ChernClassOfTrivializedBundle.main L w hI hT
