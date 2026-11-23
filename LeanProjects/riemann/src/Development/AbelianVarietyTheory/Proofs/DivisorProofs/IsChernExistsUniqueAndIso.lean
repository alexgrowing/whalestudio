import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineH2SmallCoverBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.Cris.ChernExists

variable {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {X : Scheme.{0}} {s : X ⟶ Sp R}

theorem exp_add (T : Thick γ s) {a b : T.B} (ha : a ∈ T.J) (hb : b ∈ T.J) :
    dpExp T.δ (a + b) = dpExp T.δ a * dpExp T.δ b :=
  (GlobalTheory.Cris.dpExp_add_and_natural T.B T.B T.J T.J T.δ T.δ T.nil).1 a ha b hb

theorem exp_map {T T' : Thick γ s} (φ : T ⟶ T') {a : T.B} (ha : a ∈ T.J) :
    φ.φ (dpExp T.δ a) = dpExp T'.δ (φ.φ a) :=
  (GlobalTheory.Cris.dpExp_add_and_natural T.B T'.B T.J T'.J T.δ T'.δ T.nil).2 (φ.φ : T.B →+* T'.B) φ.dp a ha

theorem exp_inj (T : Thick γ s) {a b : T.B} (ha : a ∈ T.J) (hb : b ∈ T.J)
    (h : dpExp T.δ a = dpExp T.δ b) : a = b :=
  (GlobalTheory.Cris.ExpBij.dpExp_bijOn T.B T.J T.δ T.nil).injOn ha hb h

theorem exp_surj (T : Thick γ s) {u : T.B} (hu : T.π u = 1) : ∃ a ∈ T.J, dpExp T.δ a = u :=
  (GlobalTheory.Cris.ExpBij.dpExp_bijOn T.B T.J T.δ T.nil).surjOn
    (show u - 1 ∈ T.J from (T.ker _).1 (by rw [map_sub, hu, map_one, sub_self]))

theorem isUnit_of_π (T : Thick γ s) {u : T.B} (hu : IsUnit (T.π u)) : IsUnit u := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  obtain ⟨v, rfl⟩ := T.surj v
  obtain ⟨a, ha, e⟩ := exp_surj T (u := u * v) (by rw [map_mul, hv])
  refine IsUnit.of_mul_eq_one (v * dpExp T.δ (-a)) ?_
  rw [← mul_assoc, ← e, ← exp_add T ha (T.J.neg_mem ha), add_neg_cancel, dpExp_zero]

theorem exists_log (T : Thick γ s) {a b : T.B} (hb : IsUnit (T.π b)) (h : T.π a = T.π b) :
    ∃ f ∈ T.J, dpExp T.δ f * b = a := by
  obtain ⟨v, hv⟩ := (isUnit_of_π T hb).exists_left_inv
  obtain ⟨f, hf, e⟩ := exp_surj T (u := a * v) (by rw [map_mul, h, ← map_mul, mul_comm, hv, map_one])
  exact ⟨f, hf, by rw [e, mul_assoc, hv, mul_one]⟩

universe v u
variable {C : Type u} [Category.{v} C] (G : C ⥤ Thick γ s)

theorem exists_cocycle (a : ∀ T T' : C, (T ⟶ T') → (G.obj T').B₀) (hu : ∀ T T' φ, IsUnit (a T T' φ))
    (ha : ∀ T T' T'' φ ψ, a T T'' (φ ≫ ψ) = (G.map ψ).φ₀ (a T T' φ) * a T' T'' ψ) :
    ∃ (u : ∀ T T' : C, (T ⟶ T') → (G.obj T').B) (ℓ : Z2 (G ⋙ O γ s)),
      (∀ T T' φ, (G.obj T').π (u T T' φ) = a T T' φ) ∧
      ∀ T T' T'' φ ψ, (ℓ.1 T T' T'' φ ψ : (G.obj T'').B) ∈ (G.obj T'').J ∧
        dpExp (G.obj T'').δ (ℓ.1 T T' T'' φ ψ) * u T T'' (φ ≫ ψ) =
          (G.map ψ).φ (u T T' φ) * u T' T'' ψ := by
  choose u h1 using fun T T' φ ↦ (G.obj T').surj (a T T' φ)
  choose l hl h2 using fun T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T'') ↦
    exists_log (G.obj T'') (a := (G.map ψ).φ (u T T' φ) * u T' T'' ψ) (b := u T T'' (φ ≫ ψ))
      (by rw [h1]; exact hu _ _ _) (by rw [map_mul, ← (G.map ψ).comm, h1, h1, h1, ha])
  refine ⟨u, ⟨l, fun T T' T'' T''' φ ψ χ ↦ ?_⟩, h1, fun T T' T'' φ ψ ↦ ⟨hl _ _ _ _ _, h2 _ _ _ _ _⟩⟩
  change (G.map χ).φ (l T T' T'' φ ψ) + l T T'' T''' (φ ≫ ψ) χ =
    l T T' T''' φ (ψ ≫ χ) + l T' T'' T''' ψ χ
  have m := (G.map χ).mem (hl T T' T'' φ ψ)
  refine exp_inj _ (add_mem m (hl ..)) (add_mem (hl ..) (hl ..)) ?_
  rw [exp_add _ m (hl ..), exp_add _ (hl ..) (hl ..), ← exp_map _ (hl ..)]
  have e1 := congrArg (G.map χ).φ (h2 T T' T'' φ ψ)
  have e2 := h2 T T'' T''' (φ ≫ ψ) χ
  have e3 := h2 T T' T''' φ (ψ ≫ χ)
  have e4 := h2 T' T'' T''' ψ χ
  rw [map_mul, map_mul] at e1
  rw [Category.assoc] at e2
  rw [G.map_comp, Thick.comp_φ] at e3
  have hU : IsUnit (u T T''' (φ ≫ ψ ≫ χ)) := isUnit_of_π _ (by rw [h1]; exact hu _ _ _)
  refine hU.mul_right_cancel ?_
  linear_combination (G.map χ).φ (dpExp _ (l T T' T'' φ ψ)) * e2 + u T'' T''' χ * e1 -
    dpExp _ (l T' T'' T''' ψ χ) * e3 - (G.map χ).φ ((G.map ψ).φ (u T T' φ)) * e4

theorem mk_eq_mk (u u' : ∀ T T' : C, (T ⟶ T') → (G.obj T').B) (ℓ ℓ' : Z2 (G ⋙ O γ s))
    (w : ∀ T : C, (G.obj T).B₀) (hw : ∀ T, IsUnit (w T))
    (hu : ∀ T T' φ, IsUnit ((G.obj T').π (u T T' φ)))
    (e : ∀ T T' φ, (G.obj T').π (u' T T' φ) * (G.map φ).φ₀ (w T) = w T' * (G.obj T').π (u T T' φ))
    (h : ∀ T T' T'' φ ψ, (ℓ.1 T T' T'' φ ψ : (G.obj T'').B) ∈ (G.obj T'').J ∧
        dpExp (G.obj T'').δ (ℓ.1 T T' T'' φ ψ) * u T T'' (φ ≫ ψ) =
          (G.map ψ).φ (u T T' φ) * u T' T'' ψ)
    (h' : ∀ T T' T'' φ ψ, (ℓ'.1 T T' T'' φ ψ : (G.obj T'').B) ∈ (G.obj T'').J ∧
        dpExp (G.obj T'').δ (ℓ'.1 T T' T'' φ ψ) * u' T T'' (φ ≫ ψ) =
          (G.map ψ).φ (u' T T' φ) * u' T' T'' ψ) :
    CatCoh.H2.mk _ ℓ' = CatCoh.H2.mk _ ℓ := by
  choose W hW using fun T ↦ (G.obj T).surj (w T)
  choose f hf h2 using fun T T' (φ : T ⟶ T') ↦
    exists_log (G.obj T') (a := u' T T' φ * (G.map φ).φ (W T)) (b := W T' * u T T' φ)
      (by rw [map_mul, hW]; exact (hw _).mul (hu _ _ _))
      (by rw [map_mul, map_mul, ← (G.map φ).comm, hW, hW, e])
  refine CatCoh.H2.mk_eq_mk.2 ⟨f, ?_⟩
  funext T T' T'' φ ψ
  obtain ⟨m, e4⟩ := h T T' T'' φ ψ
  obtain ⟨m', e5⟩ := h' T T' T'' φ ψ
  have key : ∀ l l' : (G.obj T'').B, l ∈ (G.obj T'').J → l' ∈ (G.obj T'').J →
      dpExp (G.obj T'').δ l * u T T'' (φ ≫ ψ) = (G.map ψ).φ (u T T' φ) * u T' T'' ψ →
      dpExp (G.obj T'').δ l' * u' T T'' (φ ≫ ψ) = (G.map ψ).φ (u' T T' φ) * u' T' T'' ψ →
      (G.map ψ).φ (f T T' φ) - f T T'' (φ ≫ ψ) + f T' T'' ψ = l' - l := by
    intro l l' m m' e4 e5
    have m1 := (G.map ψ).mem (hf T T' φ)
    have k : (G.map ψ).φ (f T T' φ) + f T' T'' ψ + l = l' + f T T'' (φ ≫ ψ) := by
      refine exp_inj _ (add_mem (add_mem m1 (hf ..)) m) (add_mem m' (hf ..)) ?_
      rw [exp_add _ (add_mem m1 (hf ..)) m, exp_add _ m1 (hf ..), exp_add _ m' (hf ..),
        ← exp_map _ (hf ..)]
      have e1 := congrArg (G.map ψ).φ (h2 T T' φ)
      have e2 := h2 T' T'' ψ
      have e3 := h2 T T'' (φ ≫ ψ)
      simp only [map_mul] at e1
      rw [G.map_comp, Thick.comp_φ] at e3
      have hWu : ∀ T, IsUnit (W T) := fun T ↦ isUnit_of_π _ (by rw [hW]; exact hw _)
      have hU : IsUnit (W T'' * u T T'' (φ ≫ ψ) * (G.map ψ).φ (W T')) :=
        ((hWu _).mul (isUnit_of_π _ (hu _ _ _))).mul ((hWu _).map _)
      refine hU.mul_right_cancel ?_
      linear_combination
        (G.map ψ).φ (dpExp _ (f T T' φ)) * dpExp _ (f T' T'' ψ) * W T'' * (G.map ψ).φ (W T') * e4 +
        dpExp _ (f T' T'' ψ) * W T'' * u T' T'' ψ * e1 +
        (G.map ψ).φ (u' T T' φ) * (G.map ψ).φ ((G.map φ).φ (W T)) * e2 -
        (G.map ψ).φ ((G.map φ).φ (W T)) * (G.map ψ).φ (W T') * e5 -
        dpExp _ l' * (G.map ψ).φ (W T') * e3
    linear_combination k
  exact key _ _ m m' e4 e5

theorem evalAt_res {B : Type} [CommRing B] (x : Sp B ⟶ X) {U V : X.Opens} (hV : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)ˣ) :
    evalAt x V h' (res hV f).val = evalAt x U h f.val := by
  have e : x.appLE U ⊤ h = X.presheaf.map (homOfLE hV).op ≫ x.appLE V ⊤ h' := by
    rw [Scheme.Hom.map_appLE]
  unfold evalAt
  rw [e]
  rfl

theorem evalAt_spMap {B B' : Type} [CommRing B] [CommRing B'] (φ : B →+* B') (x : Sp B ⟶ X)
    (x' : Sp B' ⟶ X) (e : spMap φ ≫ x = x') {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ x' ⁻¹ᵁ U)
    (f : Γ(X, U)) : φ (evalAt x U h f) = evalAt x' U h' f := by
  subst e
  have e : (spMap φ ≫ x).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of B')).hom =
      x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom ≫ CommRingCat.ofHom φ := by
    rw [← Scheme.ΓSpecIso_naturality, ← Category.assoc,
      ← Scheme.Hom.appLE_comp_appLE (spMap φ) x U ⊤ ⊤ h le_rfl]
    congr 2
  exact (congrArg (fun t ↦ t.hom f) e).symm

def evU {B : Type} [CommRing B] (x : Sp B ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U)ˣ →* Bˣ :=
  Units.map (evalAt x U h : Γ(X, U) →* B)

theorem evU_res {B : Type} [CommRing B] (x : Sp B ⟶ X) {U V : X.Opens} (hV : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)ˣ) : evU x V h' (res hV f) = evU x U h f :=
  Units.ext (evalAt_res x hV h h' f)

theorem evU_cocycle {B : Type} [CommRing B] (x : Sp B ⟶ X) {L : LB X} (hL : L.IsLB) {i j k : L.ι}
    (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) (hk : ⊤ ≤ x ⁻¹ᵁ L.U k) :
    evU x (L.U i ⊓ L.U j) (le_inf hi hj) (L.g i j) * evU x (L.U j ⊓ L.U k) (le_inf hj hk) (L.g j k) =
      evU x (L.U i ⊓ L.U k) (le_inf hi hk) (L.g i k) := by
  have h : ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L.U j ⊓ L.U k) := le_inf (le_inf hi hj) hk
  have e := congrArg (evU x (L.U i ⊓ L.U j ⊓ L.U k) h) (hL.cocycle i j k)
  rw [map_mul] at e
  exact (congrArg₂ (· * ·) (evU_res x _ _ h _) (evU_res x _ _ h _)).symm.trans
    (e.trans (evU_res x _ _ h _))

theorem evU_iso {B : Type} [CommRing B] (x : Sp B ⟶ X) {L M : LB X} {w : LB.Iso L M} (hw : w.IsGen)
    {i j : L.ι} {k l : M.ι} (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hj : ⊤ ≤ x ⁻¹ᵁ L.U j)
    (hk : ⊤ ≤ x ⁻¹ᵁ M.U k) (hl : ⊤ ≤ x ⁻¹ᵁ M.U l) :
    evU x (M.U k ⊓ M.U l) (le_inf hk hl) (M.g k l) * evU x (M.U l ⊓ L.U j) (le_inf hl hj) (w.s (l, j)) =
      evU x (M.U k ⊓ L.U i) (le_inf hk hi) (w.s (k, i)) *
        evU x (L.U i ⊓ L.U j) (le_inf hi hj) (L.g i j) := by
  have h : ⊤ ≤ x ⁻¹ᵁ (M.U k ⊓ L.U i ⊓ (M.U l ⊓ L.U j)) := le_inf (le_inf hk hi) (le_inf hl hj)
  have key : ∀ (a : Γ(X, M.U k ⊓ L.U i)ˣ) (b : Γ(X, M.U l ⊓ L.U j)ˣ),
      res (V := M.U k ⊓ L.U i ⊓ (M.U l ⊓ L.U j)) inf_le_left a =
        res (inf_le_inf inf_le_left inf_le_left) (M.g k l) *
        (res (inf_le_inf inf_le_right inf_le_right) (L.g i j))⁻¹ * res inf_le_right b →
      evU x (M.U k ⊓ M.U l) (le_inf hk hl) (M.g k l) * evU x (M.U l ⊓ L.U j) (le_inf hl hj) b =
        evU x (M.U k ⊓ L.U i) (le_inf hk hi) a * evU x (L.U i ⊓ L.U j) (le_inf hi hj) (L.g i j) := by
    intro a b e
    have e := congrArg (evU x _ h) e
    rw [map_mul, map_mul, map_inv, evU_res (U := M.U k ⊓ L.U i) x _ (le_inf hk hi) h,
      evU_res (U := M.U k ⊓ M.U l) x _ (le_inf hk hl) h,
      evU_res (U := L.U i ⊓ L.U j) x _ (le_inf hi hj) h,
      evU_res (U := M.U l ⊓ L.U j) x _ (le_inf hl hj) h] at e
    rw [e, mul_right_comm _ _⁻¹, inv_mul_cancel_right]
  exact key _ _ (hw (k, i) (l, j))

theorem exists_isChern (L : LB X) (hL : L.IsLB) : ∃ z, IsChern γ s L z := by
  let i : (IsSmall γ s L.U).FullSubcategory → L.ι := fun T ↦ T.property.choose
  have hi : ∀ T, ⊤ ≤ T.obj.x ⁻¹ᵁ L.U (i T) := fun T ↦ T.property.choose_spec
  obtain ⟨u, ℓ, h1, h2⟩ := exists_cocycle (IsSmall γ s L.U).ι
    (fun T T' φ ↦ evalAt T'.obj.x (L.U (i T') ⊓ L.U (i T))
      (le_inf (hi T') (φ.hom.le_preimage (hi T))) (L.g (i T') (i T)).val)
    (fun T T' φ ↦ (Units.isUnit _).map _) fun T T' T'' φ ψ ↦ by
      have e := congrArg Units.val (evU_cocycle T''.obj.x hL (hi T'') (ψ.hom.le_preimage (hi T'))
        ((φ ≫ ψ).hom.le_preimage (hi T)))
      refine e.symm.trans ((mul_comm _ _).trans ?_)
      exact congrArg₂ (· * ·) (evalAt_spMap ψ.hom.φ₀ T'.obj.x T''.obj.x ψ.hom.pt _ _ _).symm rfl
  obtain ⟨z, hz⟩ := (GlobalTheory.T.crystalline_H2_small_cover_bijective R I γ X s L.ι L.U hL.cover).2 (CatCoh.H2.mk _ ℓ)
  exact ⟨z, i, hi, u, ℓ, h1, h2, hz⟩

def coarsen {ι ι' : Type} (U : ι → X.Opens) (U' : ι' → X.Opens) (h : ∀ j, ∃ i, U' j ≤ U i) :
    CoefMap (RingHom.id R) ((IsSmall γ s U).ι ⋙ O γ s) ((IsSmall γ s U').ι ⋙ O γ s) where
  G := ObjectProperty.lift _ (IsSmall γ s U').ι fun T ↦
    T.property.elim fun j hj ↦ (h j).elim fun i hi ↦ ⟨i, fun p _ ↦ hi (hj (Set.mem_univ p))⟩
  α T := RingHom.id T.obj.B
  naturality _ _ := rfl
  smul _ _ _ := rfl

theorem coarsen_pull2 {ι ι' : Type} (U : ι → X.Opens) (U' : ι' → X.Opens) (h : ∀ j, ∃ i, U' j ≤ U i)
    (z : Cris.H2 γ s) :
    (coarsen U U' h).pull2 ((CoefMap.restrict (O γ s) (IsSmall γ s U).ι).pull2 z) =
      (CoefMap.restrict (O γ s) (IsSmall γ s U').ι).pull2 z := by
  obtain ⟨z, rfl⟩ := CatCoh.H2.mk_surjective _ z
  rfl

theorem eq_of_iso {L M : LB X} (hL : L.IsLB) (hM : M.IsLB) (h : LBIso L M) {z z' : Cris.H2 γ s}
    (hz : IsChern γ s L z) (hz' : IsChern γ s M z') : z' = z := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨i, hi, u, ℓ, h1, h2, h3⟩ := hz
  obtain ⟨i', hi', u', ℓ', h1', h2', h3'⟩ := hz'
  let U : M.ι × L.ι → X.Opens := fun p ↦ M.U p.1 ⊓ L.U p.2
  have hU : ⨆ p, U p = ⊤ := by
    rw [iSup_prod]
    simp only [U, ← inf_iSup_eq, hL.cover, inf_top_eq, hM.cover]
  let n := coarsen (γ := γ) (s := s) L.U U fun p ↦ ⟨p.2, inf_le_right⟩
  let n' := coarsen (γ := γ) (s := s) M.U U fun p ↦ ⟨p.1, inf_le_left⟩
  refine (GlobalTheory.T.crystalline_H2_small_cover_bijective R I γ X s _ U hU).1 ?_
  rw [← coarsen_pull2 L.U U (fun p ↦ ⟨p.2, inf_le_right⟩) z,
    ← coarsen_pull2 M.U U (fun p ↦ ⟨p.1, inf_le_left⟩) z', h3, h3', CoefMap.pullCohomologyTwo_class,
    CoefMap.pullCohomologyTwo_class]
  refine mk_eq_mk (IsSmall γ s U).ι (fun T T' φ ↦ u _ _ (n.G.map φ)) (fun T T' φ ↦ u' _ _ (n'.G.map φ))
    _ _ (fun T ↦ (evU T.obj.x (M.U (i' (n'.G.obj T)) ⊓ L.U (i (n.G.obj T)))
      (le_inf (hi' (n'.G.obj T)) (hi (n.G.obj T))) (w.s (i' (n'.G.obj T), i (n.G.obj T)))).val)
    (fun T ↦ Units.isUnit _) (fun T T' φ ↦ ?_) (fun T T' φ ↦ ?_)
    (fun T T' T'' φ ψ ↦ h2 _ _ _ (n.G.map φ) (n.G.map ψ))
    (fun T T' T'' φ ψ ↦ h2' _ _ _ (n'.G.map φ) (n'.G.map ψ))
  · exact (h1 _ _ (n.G.map φ)).symm ▸ (Units.isUnit _).map _
  · have e := congrArg Units.val (evU_iso T'.obj.x hw (hi (n.G.obj T'))
      (φ.hom.le_preimage (hi (n.G.obj T))) (hi' (n'.G.obj T')) (φ.hom.le_preimage (hi' (n'.G.obj T))))
    refine Eq.trans ?_ (e.trans ?_)
    · exact congrArg₂ (· * ·) (h1' _ _ (n'.G.map φ))
        (evalAt_spMap φ.hom.φ₀ T.obj.x T'.obj.x φ.hom.pt _ _ _)
    · exact congrArg₂ (· * ·) rfl (h1 _ _ (n.G.map φ)).symm

theorem lbIso_refl {L : LB X} (hL : L.IsLB) : LBIso L L := by
  refine ⟨⟨fun p ↦ L.g p.1 p.2⟩, fun p q ↦ ?_⟩
  have rr : ∀ {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)ˣ),
      res h' (res h a) = res (h'.trans h) a := fun h h' a ↦ Units.ext (by
    change (X.presheaf.map _ ≫ X.presheaf.map _).hom a.val = _
    rw [← X.presheaf.map_comp]; rfl)
  let W := L.U p.1 ⊓ L.U p.2 ⊓ (L.U q.1 ⊓ L.U q.2)
  have a1 : W ≤ L.U p.1 := inf_le_left.trans inf_le_left
  have a2 : W ≤ L.U p.2 := inf_le_left.trans inf_le_right
  have b1 : W ≤ L.U q.1 := inf_le_right.trans inf_le_left
  have b2 : W ≤ L.U q.2 := inf_le_right.trans inf_le_right
  have e1 := congrArg (res (le_inf (le_inf a1 a2) b2)) (hL.cocycle p.1 p.2 q.2)
  have e2 := congrArg (res (le_inf (le_inf a1 b1) b2)) (hL.cocycle p.1 q.1 q.2)
  simp only [map_mul, rr] at e1 e2
  change res (le_inf a1 a2) (L.g p.1 p.2) = res (le_inf a1 b1) (L.g p.1 q.1) *
    (res (le_inf a2 b2) (L.g p.2 q.2))⁻¹ * res (le_inf b1 b2) (L.g q.1 q.2)
  rw [mul_right_comm, e2, ← e1, mul_inv_cancel_right]

end GlobalTheory.Cris.ChernExists

namespace GlobalTheory.Cris

theorem isChern_existsUnique_and_iso (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I)
    (X : Scheme.{0}) (s : X ⟶ Sp R) :
    (∀ L : LB X, L.IsLB → ∃! z, IsChern κ s L z) ∧
      (∀ L M : LB X, L.IsLB → M.IsLB → LBIso L M → ∀ z, IsChern κ s L z → IsChern κ s M z) := by
  refine ⟨fun L hL ↦ ?_, fun L M hL hM h z hz ↦ ?_⟩
  · obtain ⟨z, hz⟩ := ChernExists.exists_isChern (γ := κ) (s := s) L hL
    exact ⟨z, hz, fun z' hz' ↦ ChernExists.eq_of_iso hL hL (ChernExists.lbIso_refl hL) hz hz'⟩
  · obtain ⟨z', hz'⟩ := ChernExists.exists_isChern (γ := κ) (s := s) M hM
    exact ChernExists.eq_of_iso hL hM h hz hz' ▸ hz'

end GlobalTheory.Cris
