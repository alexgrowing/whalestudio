import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsTranslSum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ValVEqOneIntegralGenerators
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabMapOfIsoOfExtendGen
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.NuExtA

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral.PullScalar

open TopologicalSpace IsLocalRing

abbrev PtUnit (A : Scheme.{0}) : Type 1 := ∀ (Y : Scheme.{0}) (_ : Y ⟶ A) (y : Y), (Y.presheaf.stalk y)ˣ

def Rep {A : Scheme.{0}} (W : A.Opens) (v : PtUnit A) : Prop :=
  ∃ u : Γ(A, W)ˣ, ∀ (Y : Scheme.{0}) (f : Y ⟶ A) (y : Y), f y ∈ W → gm f y W u = v Y f y

section Rep

variable {A X : Scheme.{0}} {W : A.Opens} {v w : PtUnit A}

theorem Rep.mul (h : Rep W v) (h' : Rep W w) : Rep W fun Y f y => v Y f y * w Y f y := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨u', hu'⟩ := h'
  exact ⟨u * u', fun Y f y hy => (map_mul _ _ _).trans (congrArg₂ (· * ·) (hu Y f y hy) (hu' Y f y hy))⟩

theorem Rep.zpow (h : Rep W v) (k : ℤ) : Rep W fun Y f y => v Y f y ^ k := by
  obtain ⟨u, hu⟩ := h
  exact ⟨u ^ k, fun Y f y hy => (map_zpow _ _ _).trans (congrArg (· ^ k) (hu Y f y hy))⟩

theorem Rep.inv (h : Rep W v) : Rep W fun Y f y => (v Y f y)⁻¹ := by
  obtain ⟨u, hu⟩ := h
  exact ⟨u⁻¹, fun Y f y hy => (map_inv _ _).trans (congrArg (·⁻¹) (hu Y f y hy))⟩

theorem Rep.pull (h : A ⟶ X) (U : X.Opens) (le : W ≤ h ⁻¹ᵁ U) (a : Γ(X, U)ˣ) :
    Rep W fun _ f y => gm (f ≫ h) y U a :=
  ⟨res le (pullU h U a), fun _ f y hy => (gm_res f y le hy _).trans (gm_pull f h y U (le hy) a)⟩

theorem Rep.self (U : A.Opens) (le : W ≤ U) (a : Γ(A, U)ˣ) : Rep W fun _ f y => gm f y U a :=
  ⟨res le a, fun _ f y hy => gm_res f y le hy _⟩

theorem Rep.mono (h : Rep W v) {W' : A.Opens} (le : W' ≤ W) : Rep W' v := by
  obtain ⟨u, hu⟩ := h
  exact ⟨res le u, fun Y f y hy => (gm_res f y le hy _).trans (hu Y f y (le hy))⟩

theorem Rep.iso {L : LB X} {L' : LB A} {F : A ⟶ X} (w : LB.Iso L' (L.pull F)) (j : L.ι) (k : L'.ι)
    (le : ∀ z ∈ W, F z ∈ L.U j ∧ z ∈ L'.U k) : Rep W fun _ f y => gw w f y j k :=
  Rep.self ((L.pull F).U (fun _ => j) ⊓ L'.U k) (fun z hz => ⟨mem_pull.2 (le z hz).1, (le z hz).2⟩) _

theorem Rep.iso_pull {X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F)) (h : A ⟶ X')
    (j : L.ι) (k : L'.ι) (le : ∀ z ∈ W, F (h z) ∈ L.U j ∧ h z ∈ L'.U k) :
    Rep W fun _ f y => gw w (f ≫ h) y j k :=
  Rep.pull h ((L.pull F).U (fun _ => j) ⊓ L'.U k) (fun z hz => ⟨mem_pull.2 (le z hz).1, (le z hz).2⟩) _

theorem exists_gen_of_rep {M : LB X} (hM : M.IsLB) (d : A ⟶ X) {Λ : Type} (W : Λ → A.Opens) (hW : ∀ x, ∃ κ, x ∈ W κ)
    (v : M.ι → Λ → PtUnit A) (hv : ∀ i κ, Rep (d ⁻¹ᵁ M.U i ⊓ W κ) (v i κ))
    (ht : ∀ (y : A) i i' κ κ', d y ∈ M.U i → d y ∈ M.U i' → y ∈ W κ → y ∈ W κ' →
      v i κ _ (𝟙 A) y = gm d y _ (M.g i i') * v i' κ' _ (𝟙 A) y) :
    ∃ r : LB.Gen (M.pull d), r.IsGen ∧ ∀ (Y : Scheme.{0}) (f : Y ⟶ A) (y : Y) i κ, d (f y) ∈ M.U i → f y ∈ W κ →
      gm f y ((M.pull d).U fun _ => i) (r.s fun _ => i) = v i κ Y f y := by
  choose u hu using hv
  have glue : ∀ i, ∃ s : Γ(A, (M.pull d).U fun _ => i)ˣ, ∀ (Y : Scheme.{0}) (f : Y ⟶ A) (y : Y) κ,
      d (f y) ∈ M.U i → f y ∈ W κ → gm f y _ s = v i κ Y f y := by
    intro i
    have l₀ : ∀ κ, d ⁻¹ᵁ M.U i ⊓ W κ ≤ (M.pull d).U fun _ => i := fun κ x hx => mem_pull.2 hx.1
    obtain ⟨s, hs⟩ := glue_unit _ _ l₀ (fun x hx => by
        obtain ⟨κ, hκ⟩ := hW x
        exact Opens.mem_iSup.2 ⟨κ, mem_pull.1 hx, hκ⟩) (u i) (fun κ κ' x hx => by
        rw [hu i κ _ (𝟙 A) x hx.1, hu i κ' _ (𝟙 A) x hx.2, ht x i i κ κ' hx.1.1 hx.1.1 hx.1.2 hx.2.2,
          gm_self hM d x hx.1.1, _root_.one_mul])
    refine ⟨s, fun Y f y κ h₁ h₂ => ?_⟩
    have hy : f y ∈ d ⁻¹ᵁ M.U i ⊓ W κ := ⟨h₁, h₂⟩
    exact (gm_res f y (l₀ κ) hy s).symm.trans ((congrArg (gm f y _) (hs κ)).trans (hu i κ Y f y hy))
  choose s hs using glue
  refine ⟨⟨fun J => s (J PUnit.unit)⟩, isGen_of_gm _ fun y J J' hJ hJ' => ?_, fun Y f y i κ => hs i Y f y κ⟩
  obtain ⟨κ, hκ⟩ := hW y
  have h₁ := mem_pull.1 hJ
  have h₂ := mem_pull.1 hJ'
  refine (hs _ _ (𝟙 A) y κ h₁ hκ).trans ((ht y _ _ κ κ h₁ h₂ hκ hκ).trans
    (congrArg₂ (· * ·) ?_ (hs _ _ (𝟙 A) y κ h₂ hκ).symm))
  rw [trF, Fintype.prod_unique, zpow_one, Category.id_comp]

end Rep

section Model

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {K : Type} [Field K] [Algebra V K] [IsFractionRing V K]

theorem exists_units_of_rep (G : Over (Sp V)) [GrpObj G] (hG : IsSemiAbelian G) {A : Scheme.{0}} {d : A ⟶ G.left}
    {q : A ⟶ Sp K} (hK : IsPullback d q G.hom (spMap (algebraMap V K))) {eK : Sp K ⟶ A}
    (heK : eK ≫ d = spMap (algebraMap V K) ≫ η[G].left) {M : LB G.left} (hM : M.IsLB)
    {Λ : Type} (W : Λ → A.Opens) (hW : ∀ x, ∃ κ, x ∈ W κ)
    (v : M.ι → Λ → PtUnit A) (hv : ∀ i κ, Rep (d ⁻¹ᵁ M.U i ⊓ W κ) (v i κ))
    (ht : ∀ (y : A) i i' κ κ', d y ∈ M.U i → d y ∈ M.U i' → y ∈ W κ → y ∈ W κ' →
      v i κ _ (𝟙 A) y = gm d y _ (M.g i i') * v i' κ' _ (𝟙 A) y)
    (ρ : M.ι → PtUnit (Sp V)) (hρ : ∀ i, Rep (η[G].left ⁻¹ᵁ M.U i) (ρ i))
    (hc : ∀ (y : Sp K) i, d (eK y) ∈ M.U i → ∃ κ, eK y ∈ W κ ∧ v i κ _ eK y = ρ i _ (spMap (algebraMap V K)) y) :
    ∃ B : ∀ i, Γ(G.left, M.U i)ˣ, ∀ (Y : Scheme.{0}) (f : Y ⟶ A) (y : Y) i κ, d (f y) ∈ M.U i → f y ∈ W κ →
      gm (f ≫ d) y (M.U i) (B i) = v i κ Y f y := by
  have := hG.smooth
  have := hG.geomConnected
  have := grpObj_geometricallyIntegral_of_smooth _ G
  have hs := IsPullback.of_hasPullback G.hom (Spec.map (CommRingCat.ofHom (residue V)))
  have := DvrModel.isIntegral_of_geometricallyIntegral hK
  have := DvrModel.isIntegral_of_geometricallyIntegral hs
  obtain ⟨r, hr, rv⟩ := exists_gen_of_rep hM d W hW v hv ht
  choose u hu using hρ
  let e : Sp V ⟶ G.left := η[G].left
  let ρ' : LB.Gen (M.pull e) := ⟨fun J => res (LB.wchart_le M _ J PUnit.unit) (u (J PUnit.unit))⟩
  obtain ⟨B, ⟨-, hB⟩, -⟩ := DvrModel.existsUnique_gen hK hs (e := e) (Over.w η[G]) heK hM r hr ρ' (by
    intro J J' _ _ hJ
    obtain rfl : J = J' := funext fun _ => hJ PUnit.unit PUnit.unit heK
    refine unit_ext fun y hy => ?_
    refine (gm_res _ y _ hy _).trans (Eq.trans ?_ (gm_res _ y _ hy _).symm)
    refine (gm_pullGen _ _ _ r _ (𝟙 _) y J hy.1).trans (Eq.trans ?_ (gm_pullGen _ _ _ ρ' _ (𝟙 _) y J hy.2).symm)
    have h₁ : d (eK y) ∈ M.U (J PUnit.unit) := Set.mem_iInter.1 hy.1 PUnit.unit
    have h₂ : e (spMap (algebraMap V K) y) ∈ M.U (J PUnit.unit) := Set.mem_iInter.1 hy.2 PUnit.unit
    obtain ⟨κ, hκ, hcκ⟩ := hc y _ h₁
    rw [Category.id_comp, Category.id_comp]
    exact (rv _ eK y _ κ h₁ hκ).trans (hcκ.trans ((hu _ _ _ y h₂).symm.trans
      (gm_res _ y _ (mem_pull.2 h₂) _).symm)))
  refine ⟨B.s, fun Y f y i κ h₁ h₂ => Eq.trans ?_ (rv Y f y i κ h₁ h₂)⟩
  rw [← hB]
  exact ((gm_res f y _ (mem_pull.2 h₁) _).trans (gm_pull f d y (M.U i) h₁ _)).symm

theorem not_vanish (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) {L : LB G.left}
    (θ : LB.Sec L) (hθ : ∀ σ : LB.Sec L, ∃! a : V, ∀ i, σ.f i = constFn G.hom _ a * θ.f i) {N : ℕ}
    (hN : IsUnit (N : V))
    (h : ∀ x : G.left, G.hom x = closedPoint V → ∀ i, (𝟙 G ^ N).left x ∉ G.left.basicOpen (θ.f i)) : False := by
  have := hG.smooth
  have := hG.geomConnected
  have := grpObj_geometricallyIntegral_of_smooth _ G
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hs := IsPullback.of_hasPullback G.hom (Spec.map (CommRingCat.ofHom (residue V)))
  have hi := DvrModel.isIntegral_of_geometricallyIntegral hs
  have : Etale (𝟙 G ^ N).left := GrpTangent.etale_id_pow G (by simpa using hN.map (toΓ V))
  have sp : ∀ x : G.left, G.hom x = closedPoint V → _ := fun x hx =>
    (DvrModel.notMem_basicOpen_iff_specializes hϖ hs x).1 ((DvrModel.notMem_basicOpen_iff _ hϖ x).2 hx)
  generalize hξ : pullback.fst G.hom (Spec.map (CommRingCat.ofHom (residue V))) (genericPoint _) = ξ at sp
  have hξ' : G.hom ξ = closedPoint V := (DvrModel.mem_range_special hs ξ).1 ⟨_, hξ⟩
  let e : Sp V ⟶ G.left := η[G].left
  have e₁ : e ≫ (𝟙 G ^ N).left = e := by
    have : (1 : 𝟙_ _ ⟶ G) ≫ 𝟙 G ^ N = 1 := by rw [MonObj.comp_pow, Category.comp_id, one_pow]
    simpa [Hom.one_def] using congrArg (fun z => z.left) this
  have e₂ : e ≫ G.hom = 𝟙 _ := Over.w η[G]
  have s₁ : ξ ⤳ (𝟙 G ^ N).left (e (closedPoint V)) := by
    have a₁ : (𝟙 G ^ N).left (e (closedPoint V)) = e (closedPoint V) := congrArg (fun g => g (closedPoint V)) e₁
    rw [a₁]
    exact sp _ (congrArg (fun g => g (closedPoint V)) e₂)
  obtain ⟨x', -, hx'⟩ := Flat.generalizingMap (𝟙 G ^ N).left s₁
  have hv : ∀ i, ξ ∉ G.left.basicOpen (θ.f i) := fun i => hx' ▸ h x' (by
    rw [← hξ', ← hx']
    exact (congrArg (fun g => g x') (Over.w (𝟙 G ^ N))).symm) i
  obtain ⟨σ, hσ⟩ := DVR.exists_div_sec_of_thick G.hom (maximalIdeal V) hϖ.ne_zero hϖ.maximalIdeal_eq.le θ
    (fun j z hz => by
      have : IsReduced (pullback G.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal V))))) :=
        inferInstanceAs (IsReduced (pullback G.hom (Spec.map (CommRingCat.ofHom (residue V)))))
      have z₀ : ((pullback.fst G.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal V))))).app
          (L.U j)).hom (θ.f j) = 0 := by
        rw [← basicOpen_eq_bot_iff, eq_bot_iff]
        intro w hw
        rw [← Scheme.preimage_basicOpen] at hw
        exact hv j ((sp _ ((DvrModel.mem_range_special hs _).1 ⟨w, rfl⟩)).mem_open (Scheme.basicOpen _ _).isOpen hw)
      rw [gs_eq _ _ _ hz, z₀, map_zero]
      exact dvd_zero _)
  obtain ⟨b, hb, -⟩ := hθ σ
  have one : ∀ k, θ.f k = constFn G.hom _ (ϖ * b) * θ.f k := fun k => by
    conv_lhs => rw [hσ k, hb k]
    rw [← _root_.mul_assoc, DVR.constFn_eq_strMap, DVR.constFn_eq_strMap, DVR.constFn_eq_strMap, map_mul]
  have one' : ∀ k, θ.f k = constFn G.hom _ 1 * θ.f k := fun k => by
    rw [DVR.constFn_eq_strMap, map_one, _root_.one_mul]
  exact hϖ.not_isUnit (IsUnit.of_mul_eq_one _ ((hθ θ).unique one one'))

theorem notMem_basicOpen_of_generic {H A : Scheme.{0}} {p : H ⟶ Sp V} [Flat p] {d : A ⟶ H} {q : A ⟶ Sp K}
    (hK : IsPullback d q p (spMap (algebraMap V K))) {U : H.Opens} (α δ : Γ(H, U)) {a : K}
    (ha : a ∉ Set.range (algebraMap V K)) (h : ∀ z, d z ∈ U → cst q z a * gs d z U α = gs d z U δ) {x : H}
    (hx : p x = closedPoint V) : x ∉ H.basicOpen α := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have a₀ : a ≠ 0 := fun e => ha ⟨0, by rw [e, map_zero]⟩
  obtain ⟨c, hc⟩ : IsLocalization.IsInteger V a⁻¹ := (ValuationRing.isInteger_or_isInteger V a).resolve_left ha
  have hu : c ∈ maximalIdeal V := fun hu => by
    obtain ⟨u, rfl⟩ := hu
    exact ha ⟨(u⁻¹ : Vˣ), by rw [map_units_inv, hc, inv_inv]⟩
  rw [hϖ.maximalIdeal_eq] at hu
  obtain ⟨c', rfl⟩ := Ideal.mem_span_singleton.1 hu
  have e : α = constFn p U (ϖ * c') * δ := Exist.CubicalExtension.app_injective_generic hK U (fn_ext fun z hz => by
    refine (gs_pull (𝟙 A) d z U hz _).trans (Eq.trans ?_ (gs_pull (𝟙 A) d z U hz _).symm)
    rw [Category.id_comp, gs_mul d z U hz, gs_constFn p U d z hz, hK.w, cst_comp, hc, ← h z hz, ← _root_.mul_assoc,
      ← H1.cst_mul, inv_mul_cancel₀ a₀, H1.cst_one, _root_.one_mul])
  rw [e, DVR.constFn_eq_strMap, map_mul, Scheme.basicOpen_mul, Scheme.basicOpen_mul]
  intro hx'
  exact (DvrModel.notMem_basicOpen_iff p hϖ x).2 hx
    ((H.basicOpen_res _ (homOfLE (le_top : U ≤ ⊤)).op).le hx'.1.1).2

end Model

section Points

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def rigVal {S : Scheme.{0}} (t : SAB H S) (j : t.PP.L.ι) : PtUnit S := fun _ f y =>
  gm (X := (𝟙_ (Over S)).left) f y (LB.wchart t.PP.L (fun _ : PUnit => eSec t.G) fun _ => j) (t.PP.rig.s fun _ => j)

theorem rep_rigVal {S : Scheme.{0}} (t : SAB H S) (j : t.PP.L.ι) {W : S.Opens}
    (le : ∀ y ∈ W, eSec t.G y ∈ t.PP.L.U j) : Rep W (rigVal t j) :=
  Rep.self (A := S) (LB.wchart t.PP.L (fun _ : PUnit => eSec t.G) fun _ => j)
    (fun y hy => Set.mem_iInter.2 fun _ => le y hy) _

theorem rigVal_eq {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} {m : SABMap t' t f}
    {w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)} (h : RigIso m w) (e : S' ⟶ t'.G.left) (he : e = eSec t'.G) (y : S')
    (j : t.PP.L.ι) (k : t'.PP.L.ι) (hj : m.φ (e y) ∈ t.PP.L.U j) (hk : e y ∈ t'.PP.L.U k) :
    rigVal t j _ f y = gw w e y j k * rigVal t' k _ (𝟙 S') y := by
  subst he
  have e₁ := ((IntegralGenerator.rigIso_iff m w).1 h).2 _ (𝟙 _) y (fun _ => j) (fun _ => k) (fun _ => hj) (fun _ => hk)
  rw [Fintype.prod_unique, zpow_one, Category.id_comp, Category.id_comp, m.base] at e₁
  exact e₁

theorem exists_units_quot {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {K : Type} [Field K] [Algebra V K] [IsFractionRing V K] {X₀ : Scheme.{0}} {L₀ : LB X₀} (hL₀ : L₀.IsLB)
    {G G' : SAB H (Sp V)} {t t' : SAB H (Sp K)} {m₂ : SABMap t G (spMap (algebraMap V K))}
    {n₂ : SABMap t' G' (spMap (algebraMap V K))} {m₁ : t.G.left ⟶ X₀} {n₁ : t'.G.left ⟶ X₀}
    {w₁ : LB.Iso t.PP.L (L₀.pull m₁)} {w₁' : LB.Iso t'.PP.L (L₀.pull n₁)} {w₂ : LB.Iso t.PP.L (G.PP.L.pull m₂.φ)}
    {w₂' : LB.Iso t'.PP.L (G'.PP.L.pull n₂.φ)} (h₁ : PGen w₁) (h₁' : PGen w₁') (h₂ : RigIso m₂ w₂) (h₂' : RigIso n₂ w₂')
    {ψ : t.G.left ⟶ t'.G.left} {F : G.G.left ⟶ G'.G.left} (hψ : ψ ≫ n₂.φ = m₂.φ ≫ F) (eK : Sp K ⟶ t.G.left)
    (heK : eK = eSec t.G) (eψ : eK ≫ ψ = eSec t'.G) (eF : eSec G.G ≫ F = eSec G'.G) (k : ℤ)
    (b : L₀.ι → L₀.ι → PtUnit t.G.left) (hb : ∀ j j', Rep (m₁ ⁻¹ᵁ L₀.U j ⊓ ψ ⁻¹ᵁ n₁ ⁻¹ᵁ L₀.U j') (b j j'))
    (tb : ∀ (z : t.G.left) j j' i i', m₁ z ∈ L₀.U j → n₁ (ψ z) ∈ L₀.U j' → m₁ z ∈ L₀.U i → n₁ (ψ z) ∈ L₀.U i' →
      b j j' _ (𝟙 _) z = gm (𝟙 _ ≫ m₁) z _ (L₀.g j i) ^ k * gm ((𝟙 _ ≫ ψ) ≫ n₁) z _ (L₀.g j' i') ^ (-1 : ℤ) *
        b i i' _ (𝟙 _) z)
    (rb : ∀ (z : Sp K) κ κ', eK z ∈ t.PP.L.U κ → ψ (eK z) ∈ t'.PP.L.U κ' → ∃ j j', m₁ (eK z) ∈ L₀.U j ∧
      n₁ (ψ (eK z)) ∈ L₀.U j' ∧ b j j' _ eK z = (gw w₁ eK z j κ * rigVal t κ _ (𝟙 _) z) ^ k *
        (gw w₁' (eK ≫ ψ) z j' κ' * rigVal t' κ' _ (𝟙 _) z) ^ (-1 : ℤ))
    (ν' : G'.PP.L.ι) (ν : G.PP.L.ι) :
    ∃ B : Γ(G.G.left, F ⁻¹ᵁ G'.PP.L.U ν' ⊓ G.PP.L.U ν)ˣ, ∀ (z : t.G.left) j j' κ κ',
      m₂.φ z ∈ F ⁻¹ᵁ G'.PP.L.U ν' ⊓ G.PP.L.U ν → m₁ z ∈ L₀.U j → n₁ (ψ z) ∈ L₀.U j' → z ∈ t.PP.L.U κ →
      ψ z ∈ t'.PP.L.U κ' → gm m₂.φ z _ B = (b j j' _ (𝟙 _) z)⁻¹ * gw w₁ (𝟙 _) z j κ ^ k * (gw w₂ (𝟙 _) z ν κ ^ k)⁻¹ *
        (gw w₁' (𝟙 _ ≫ ψ) z j' κ')⁻¹ * gw w₂' (𝟙 _ ≫ ψ) z ν' κ' := by
  have pψ : ∀ z ν', F (m₂.φ z) ∈ G'.PP.L.U ν' → n₂.φ (ψ z) ∈ G'.PP.L.U ν' := fun z ν' =>
    (congrArg (fun q => q z ∈ G'.PP.L.U ν') hψ).mpr
  let P : LB G.G.left := LB.LinComb G.PP.L (fun _ : Fin 1 => 𝟙 _) fun _ => k
  let Q : LB G.G.left := LB.div (G'.PP.L.pull F) P
  have mQ : ∀ (i : Q.ι) z, z ∈ Q.U i → F z ∈ G'.PP.L.U (i.1 PUnit.unit) ∧ z ∈ G.PP.L.U (i.2 0) :=
    fun i z hz => ⟨mem_pull.1 hz.1, Set.mem_iInter.1 hz.2 0⟩
  let W : (t.PP.L.ι × t'.PP.L.ι) × L₀.ι × L₀.ι → t.G.left.Opens := fun κ =>
    (t.PP.L.U κ.1.1 ⊓ ψ ⁻¹ᵁ t'.PP.L.U κ.1.2) ⊓ (m₁ ⁻¹ᵁ L₀.U κ.2.1 ⊓ ψ ⁻¹ᵁ n₁ ⁻¹ᵁ L₀.U κ.2.2)
  obtain ⟨g₂, -⟩ := (IntegralGenerator.rigIso_iff _ _).1 h₂
  obtain ⟨g₂', -⟩ := (IntegralGenerator.rigIso_iff _ _).1 h₂'
  obtain ⟨B, hB⟩ := exists_units_of_rep G.G G.semi m₂.cart.1 (eK := eK)
    (heK ▸ m₂.cm.e_comm.trans (congrArg (· ≫ _) m₂.base)) (M := Q)
    (LB.isLB_div (pull_isLB G'.PP.isLB _) (LB.isLB_linComb G.PP.isLB _ _)) W
    (fun z => by
      obtain ⟨κ, hκ⟩ := exists_chart t.PP.isLB z
      obtain ⟨κ', hκ'⟩ := exists_chart t'.PP.isLB (ψ z)
      obtain ⟨j, hj⟩ := exists_chart hL₀ (m₁ z)
      obtain ⟨j', hj'⟩ := exists_chart hL₀ (n₁ (ψ z))
      exact ⟨((κ, κ'), j, j'), ⟨hκ, hκ'⟩, hj, hj'⟩)
    (fun i κ _ r z => (b κ.2.1 κ.2.2 _ r z)⁻¹ * gw w₁ r z κ.2.1 κ.1.1 ^ k * (gw w₂ r z (i.2 0) κ.1.1 ^ k)⁻¹ *
      (gw w₁' (r ≫ ψ) z κ.2.2 κ.1.2)⁻¹ * gw w₂' (r ≫ ψ) z (i.1 PUnit.unit) κ.1.2)
    (fun i κ => by
      refine Rep.mul (Rep.mul (Rep.mul (Rep.mul (Rep.inv ((hb _ _).mono fun z hz => ?_))
        (Rep.zpow (Rep.iso _ _ _ fun z hz => ?_) k)) (Rep.inv (Rep.zpow (Rep.iso _ _ _ fun z hz => ?_) k)))
        (Rep.inv (Rep.iso_pull _ _ _ _ fun z hz => ?_))) (Rep.iso_pull _ _ _ _ fun z hz => ?_)
      exacts [hz.2.2, ⟨hz.2.2.1, hz.2.1.1⟩, ⟨(mQ i _ hz.1).2, hz.2.1.1⟩, ⟨hz.2.2.2, hz.2.1.2⟩,
        ⟨pψ z _ (mQ i _ hz.1).1, hz.2.1.2⟩])
    (fun z i i' κ κ' hi hi' hκ hκ' => by
      have e₀ := gm_div_g (L := G'.PP.L) (L' := P) (F := F) m₂.φ z _ _ i.2 i'.2 (mQ i _ hi).1 (mQ i' _ hi').1
        hi.2 hi'.2
      have e₀' := gm_linComb G.PP.L (fun _ : Fin 1 => 𝟙 _) (fun _ => k) m₂.φ z i.2 i'.2 hi.2 hi'.2
      rw [Fin.prod_univ_one, Category.comp_id] at e₀'
      have e₁ := tb z _ _ _ _ hκ.2.1 hκ.2.2 hκ'.2.1 hκ'.2.2
      have e₂ := h₁ _ (𝟙 _) z _ _ _ _ hκ.2.1 hκ'.2.1 hκ.1.1 hκ'.1.1
      have e₃ := g₂ _ (𝟙 _) z _ _ _ _ (mQ i _ hi).2 (mQ i' _ hi').2 hκ.1.1 hκ'.1.1
      have e₄ := h₁' _ (𝟙 _ ≫ ψ) z _ _ _ _ hκ.2.2 hκ'.2.2 hκ.1.2 hκ'.1.2
      have e₅ := g₂' _ (𝟙 _ ≫ ψ) z _ _ _ _ (pψ z _ (mQ i _ hi).1) (pψ z _ (mQ i' _ hi').1) hκ.1.2 hκ'.1.2
      rw [Category.assoc, hψ, Category.id_comp (m₂.φ ≫ _)] at e₅
      rw [Category.id_comp m₂.φ] at e₃
      refine Eq.trans ?_ (congrArg₂ (· * ·) (e₀.trans (congrArg₂ (· * ·) rfl (congrArg (·⁻¹) e₀'))) rfl).symm
      rw [e₁, e₂, e₃, e₄, e₅]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      module)
    (fun i _ r z => rigVal G' (i.1 PUnit.unit) _ r z * (rigVal G (i.2 0) _ r z ^ k)⁻¹)
    (fun i => by
      refine Rep.mul (rep_rigVal _ _ fun z hz => ?_) (Rep.inv (Rep.zpow (rep_rigVal _ _ fun z hz => ?_) k))
      exacts [(congrArg (fun q => q z ∈ G'.PP.L.U _) eF).mp (mQ i _ hz).1, (mQ i _ hz).2])
    (fun z i hi => by
      obtain ⟨κ, hκ⟩ := exists_chart t.PP.isLB (eK z)
      obtain ⟨κ', hκ'⟩ := exists_chart t'.PP.isLB (ψ (eK z))
      obtain ⟨j, j', hj, hj', e⟩ := rb z κ κ' hκ hκ'
      refine ⟨((κ, κ'), j, j'), ⟨⟨hκ, hκ'⟩, hj, hj'⟩, ?_⟩
      have r₂ := rigVal_eq h₂ eK heK z _ κ (mQ i _ hi).2 hκ
      have r₄ := rigVal_eq h₂' _ eψ z (i.1 PUnit.unit) κ' (pψ _ _ (mQ i _ hi).1) hκ'
      dsimp only
      rw [e, r₂, r₄]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      module)
  have le : F ⁻¹ᵁ G'.PP.L.U ν' ⊓ G.PP.L.U ν ≤ Q.U (fun _ => ν', fun _ => ν) := fun z hz =>
    ⟨mem_pull.2 hz.1, Set.mem_iInter.2 fun _ => hz.2⟩
  refine ⟨res le (B _), fun z j j' κ κ' hz hj hj' hκ hκ' => (gm_res _ z le hz _).trans ?_⟩
  have := hB _ (𝟙 _) z (fun _ => ν', fun _ => ν) ((κ, κ'), j, j') (le hz) ⟨⟨hκ, hκ'⟩, hj, hj'⟩
  rwa [Category.id_comp m₂.φ] at this

variable {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

theorem exists_toFibre {K : Type} [CommRing K] {x : Sp K ⟶ Xo.X} {t : SAB H (Sp K)} (m : SABMap t Xo.univ.t x) :
    ∃ g : t.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m.φ ∧
      g ≫ (fst (Over.mk x) Xo.univ.t.G).left = t.G.hom :=
  let a0 : Over.mk (t.G.hom ≫ x) ⟶ Over.mk x := Over.homMk t.G.hom rfl
  let b0 : Over.mk (t.G.hom ≫ x) ⟶ Xo.univ.t.G := Over.homMk m.φ m.cart.1.w
  ⟨(lift a0 b0).left, congrArg (fun q => q.left) (lift_snd a0 b0), congrArg (fun q => q.left) (lift_fst a0 b0)⟩

theorem theta_pt (I : IntData Xo c T io y.1) {g : I.t'.G.left ⟶ Gx (xOf y)}
    (g₁ : g ≫ (snd (Over.mk (xOf y)) Xo.univ.t.G).left = I.m1.φ)
    (g₂ : g ≫ (fst (Over.mk (xOf y)) Xo.univ.t.G).left = I.t'.G.hom) {Z : Scheme.{0}} (r : Z ⟶ I.t'.G.left) (z : Z)
    (j : Xo.univ.t.PP.L.ι) (ν : I.G.PP.L.ι) (κ : I.t'.PP.L.ι) (hj : I.m1.φ (r z) ∈ Xo.univ.t.PP.L.U j)
    (hν : I.m2.φ (r z) ∈ I.G.PP.L.U ν) (hκ : r z ∈ I.t'.PP.L.U κ) :
    letI := io.toAlgebra
    ∃ τ, gs (r ≫ g) z ((PPx (xOf y)).U fun _ => j) (y.1.s.f fun _ => j) = (gw I.w1 r z j κ).val * τ ∧
      gs (r ≫ I.m2.φ) z _ (I.θ.f ν) = (gw I.w2 r z ν κ).val * τ := by
  letI := io.toAlgebra
  have le : (Xo.univ.t.PP.L.pull I.m1.φ).U (fun _ => j) ≤ g ⁻¹ᵁ (PPx (xOf y)).U (fun _ => j) := fun z hz =>
    Set.mem_iInter.2 fun _ => (congrArg (fun q => q z ∈ Xo.univ.t.PP.L.U j) g₁).mpr (mem_pull.1 hz)
  refine ⟨_, ?_, (IntegralGenerator.pullSec_pt I.pull r z ν hν).symm.trans
    (IntegralGenerator.isoMaps_pt I.maps2 r z ν κ hν hκ)⟩
  rw [← IntegralGenerator.isoMaps_pt I.maps1 r z j κ hj hκ, I.gen1 g g₁ g₂ (fun _ => j) le]
  exact (gs_appLE g _ _ _ r z (mem_pull.2 hj) _).symm

theorem sv_zCast {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : RigLB A) {T : Over S} {k₁ k₂ : ℤ} (h : k₁ = k₂)
    (F : LB.Sec (LPow A L.L k₁ T)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) (J) :
    sv A L (PullbackSections.zCast A h F) r z J = sv A L F r z J := by
  subst h; rfl

theorem tie_pt (I : IntData Xo c T io y.1) {g : I.t'.G.left ⟶ Gx (xOf y)}
    (g₁ : g ≫ (snd (Over.mk (xOf y)) Xo.univ.t.G).left = I.m1.φ)
    (g₂ : g ≫ (fst (Over.mk (xOf y)) Xo.univ.t.G).left = I.t'.G.hom) {M : ℕ}
    {t : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk (xOf y)))} {σ}
    (h : PullbackSections.SecTie I (M ^ 2) (PullbackSections.zCast Xo.univ.t.G (PullbackSections.natCast_sq M) t) σ)
    {Z : Scheme.{0}} (r : Z ⟶ I.t'.G.left) (z : Z) {J} (hJ : Good Xo.univ.t.PP.L z J)
    (ν : I.G.PP.L.ι) (κ : I.t'.PP.L.ι) (hν : I.m2.φ (r z) ∈ I.G.PP.L.U ν) (hκ : r z ∈ I.t'.PP.L.U κ) :
    ∃ τ, sv Xo.univ.t.G Xo.univ.t.PP t (r ≫ g) z J = (gw I.w1 r z (J (r ≫ I.m1.φ)) κ ^ (M : ℤ) ^ 2).val * τ ∧
      gs (r ≫ I.m2.φ) z (LB.wchart I.G.PP.L (fun _ : Fin 1 => 𝟙 I.G.G.left) fun _ => ν) (σ.f fun _ => ν) =
        (gw I.w2 r z ν κ ^ (M : ℤ) ^ 2).val * τ := by
  obtain ⟨σt, t₁, t₂⟩ := h
  obtain ⟨JG, hG, eG⟩ := exists_good _ I.G.PP.isLB z (K := PUnit) (fun _ => r ≫ I.m2.φ) (fun _ => ν)
    (fun _ _ _ => rfl) (fun _ => hν)
  obtain ⟨JA, hA, eA⟩ := exists_good _ I.t'.PP.isLB z (K := PUnit) (fun _ => r ≫ 𝟙 _) (fun _ => κ)
    (fun _ _ _ => rfl) (fun _ => hκ)
  have a₁ := t₁ Z r (r ≫ g) (by rw [Category.assoc]; exact congrArg (r ≫ ·) g₁)
    (by rw [Category.assoc]; exact congrArg (r ≫ ·) g₂) z J JA hJ hA
  have a₂ := t₂ Z r z JG JA hG hA
  rw [eA PUnit.unit] at a₁ a₂
  rw [eG PUnit.unit, sval_of σ _ z JG (fun _ => ν) (fun _ => by rw [Category.comp_id]; exact eG PUnit.unit)] at a₂
  refine ⟨sval σt r z JA, (sv_zCast _ _ (PullbackSections.natCast_sq M) t _ z J).symm.trans (a₁.trans ?_), a₂.trans ?_⟩ <;>
  · rw [← Nat.cast_pow, zpow_natCast, Units.val_pow_eq_pow_val]
    rfl

end Points

theorem units_mul_relation_rearrange_commRing {R : Type} [CommRing R] {A₁ A₂ A₃ A₄ A₅ : Rˣ} {a τ τ' : R}
    (h : A₁.val * τ = a * (A₃.val * τ') * A₅.val) :
    a * (A₄.val * τ') = (A₅⁻¹ * A₁ * A₂⁻¹ * A₃⁻¹ * A₄).val * (A₂.val * τ) := by
  simp only [Units.val_mul]
  linear_combination (-((A₅⁻¹).val * (A₃⁻¹).val * A₄.val)) * h -
    ((A₅⁻¹).val * A₁.val * (A₃⁻¹).val * A₄.val * τ) * A₂.inv_mul -
    (a * A₄.val * τ') * A₅.inv_mul - (a * A₄.val * τ' * (A₅⁻¹).val * A₅.val) * A₃.inv_mul

set_option maxHeartbeats 800000 in

theorem mem_range_of_reg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y y' : IntFr Xo c T io) (I : IntData Xo c T io y.1) (I' : IntData Xo c T io y'.1) (f : Fib Xo (xOf y) ⟶ Fib Xo (xOf y')) (F : I.G.G ⟶ I'.G.G) (F' : I'.G.G ⟶ I.G.G) (N M : ℕ) (a : T.Fr) (t : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk (xOf y)))), IsMonHom F → IsMonHom F' → Ext I.m1 I.m2 I'.m1 I'.m2 f F → F' ≫ F = 𝟙 _ ^ N → IsUnit (N : T.V) → letI := io.toAlgebra; IsPullOf M f a y'.1.s t → Reg I M t → a ∈ Set.range (algebraMap T.V T.Fr) := by
  intro E _ _ _ H Dw l Xo c T io y y' I I' f F F' N M a t hF hF' ⟨ψ, hψ, hψ₂, hψ₁⟩ hFF hN
    ⟨β, s'', ⟨_, hβ, hrig⟩, hs'', hcar⟩ ⟨σ, hσ⟩
  letI := io.toAlgebra
  by_contra ha
  obtain ⟨g, g₁, g₂⟩ := exists_toFibre (x := xOf y) I.m1
  obtain ⟨g', g₁', g₂'⟩ := exists_toFibre (x := xOf y') I'.m1
  have hg : g ≫ conj (xOf y) (xOf y') f.left = ψ.left ≫ g' := by
    have := hψ₁ (g ≫ (swap _).hom) (g' ≫ (swap _).hom) (by rw [Category.assoc, swap_hom_fst]; exact g₁)
      (by rw [Category.assoc, swap_hom_snd]; exact g₂) (by rw [Category.assoc, swap_hom_fst]; exact g₁')
      (by rw [Category.assoc, swap_hom_snd]; exact g₂')
    rw [conj_apply, ← Category.assoc, ← Category.assoc]
    exact (Iso.comp_inv_eq _).2 (this.trans (Category.assoc _ _ _).symm)
  generalize conj (xOf y) (xOf y') f.left = Ψ at β hβ hrig hcar hg
  have φ₀ : ∀ {Z : Scheme.{0}} (r : Z ⟶ I.t'.G.left), (r ≫ g) ≫ isoφ Xo.univ.t.G Ψ 0 = r ≫ I.m1.φ := fun r => by
    rw [Category.assoc]; exact congrArg (r ≫ ·) g₁
  have φ₁ : ∀ {Z : Scheme.{0}} (r : Z ⟶ I.t'.G.left),
      (r ≫ g) ≫ isoφ Xo.univ.t.G Ψ 1 = (r ≫ ψ.left) ≫ I'.m1.φ := fun r => by
    rw [← g₁', Category.assoc, Category.assoc, ← reassoc_of% hg]; rfl
  have hb : ∀ {Z : Scheme.{0}} (r : Z ⟶ I.t'.G.left) (z : Z) j j', I.m1.φ (r z) ∈ Xo.univ.t.PP.L.U j →
      I'.m1.φ (ψ.left (r z)) ∈ Xo.univ.t.PP.L.U j' →
      (r ≫ g) z ∈ LB.wchart Xo.univ.t.PP.L (isoφ Xo.univ.t.G Ψ) ![j, j'] := fun r z j j' hj hj' =>
    Set.mem_iInter.2 fun k => by
      fin_cases k
      · exact (congrArg (fun q => q z ∈ Xo.univ.t.PP.L.U j) (φ₀ r)).mpr hj
      · exact (congrArg (fun q => q z ∈ Xo.univ.t.PP.L.U j') (φ₁ r)).mpr hj'
  let b : Xo.univ.t.PP.L.ι → Xo.univ.t.PP.L.ι → PtUnit I.t'.G.left := fun j j' _ r z =>
    gm (r ≫ g) z (LB.wchart Xo.univ.t.PP.L (isoφ Xo.univ.t.G Ψ) ![j, j']) (β.s ![j, j'])
  have bv : ∀ {Z : Scheme.{0}} (r : Z ⟶ I.t'.G.left) (z : Z) J,
      val β (r ≫ g) z J = b (J (r ≫ I.m1.φ)) (J ((r ≫ ψ.left) ≫ I'.m1.φ)) _ r z := fun r z J =>
    val_of β _ z J _ fun k => by
      fin_cases k
      exacts [congrArg J (φ₀ r), congrArg J (φ₁ r)]
  let eK : Sp T.Fr ⟶ I.t'.G.left := eSec I.t'.G
  have eψ : eK ≫ ψ.left = eSec I'.t'.G := congrArg (fun z => z.left) (IsMonHom.one_hom ψ)
  have eF : eSec I.G.G ≫ F.left = eSec I'.G.G := congrArg (fun z => z.left) (IsMonHom.one_hom F)
  have hB := exists_units_quot Xo.univ.t.PP.isLB ((IntegralGenerator.rigIso_iff _ _).1 I.rig1).1
    ((IntegralGenerator.rigIso_iff _ _).1 I'.rig1).1 I.rig2 I'.rig2 hψ₂ eK rfl eψ eF ((M : ℤ) ^ 2) b
    (fun j j' => by
      refine Rep.pull g (LB.wchart Xo.univ.t.PP.L (isoφ Xo.univ.t.G Ψ) ![j, j']) (fun z hz => ?_) _
      exact hb (𝟙 _) z _ _ hz.1 hz.2)
    (fun z j j' i i' hj hj' hi hi' => by
      have e₁ := gen_trans hβ (𝟙 _ ≫ g) z (hb (𝟙 _) z _ _ hj hj') (hb (𝟙 _) z _ _ hi hi')
      rw [trF, Fin.prod_univ_two, φ₀, φ₁] at e₁
      exact e₁)
    (fun z κ κ' hκ hκ' => by
      choose J hJ using fun χ : Sp T.Fr ⟶ Xo.univ.t.G.left => exists_chart Xo.univ.t.PP.isLB (χ z)
      refine ⟨J (eK ≫ I.m1.φ), J ((eK ≫ ψ.left) ≫ I'.m1.φ), hJ _, hJ _, ?_⟩
      have c₁ : eK ≫ I.m1.φ = xOf y ≫ eSec _ := I.m1.cm.e_comm.trans (congrArg (· ≫ _) I.m1.base)
      have c₂ : (eK ≫ ψ.left) ≫ I'.m1.φ = xOf y' ≫ eSec _ :=
        (congrArg (· ≫ _) eψ).trans (I'.m1.cm.e_comm.trans (congrArg (· ≫ _) I'.m1.base))
      have c₃ : 𝟙 _ ≫ (ptSecT Xo.univ.t.G (1 : Over.mk (xOf y) ⟶ _)).left = eK ≫ g := by
        refine gx_ext ?_ ?_
        · rw [Category.assoc, Category.assoc, g₂, ptSecT, lift_l_fst]
          exact (Category.id_comp _).trans (Over.w η[I.t'.G]).symm
        · rw [Category.assoc, Category.assoc, g₁, ptSecT, lift_l_snd, c₁]
          exact Category.id_comp _
      have e₁ := (val_pull hJ _ _ _).symm.trans ((val_corr hJ hrig (𝟙 _)).trans (val_mul hJ _ _ _))
      have e₂ := (bv eK z J).symm.trans ((congrArg (fun q => val β q z J) c₃).symm.trans (e₁.trans
        (congrArg₂ (· * ·) (val_rigT (Over.mk (xOf y)) _ (𝟙 _) z hJ) (val_rigT (Over.mk (xOf y')) _ (𝟙 _) z hJ))))
      have r₁ := rigVal_eq I.rig1 eK rfl z _ κ (hJ (eK ≫ I.m1.φ)) hκ
      have r₃ := rigVal_eq I'.rig1 _ eψ z _ κ' (hJ ((eK ≫ ψ.left) ≫ I'.m1.φ)) hκ'
      have v₁ := (val_of (φ := fun _ : PUnit => eSec Xo.univ.t.G) (ε := fun _ => 1) Xo.univ.t.PP.rig
        (xOf y) z J _ (fun _ => congrArg J c₁.symm)).trans r₁
      have v₂ := (val_of (φ := fun _ : PUnit => eSec Xo.univ.t.G) (ε := fun _ => 1) Xo.univ.t.PP.rig
        (xOf y') z J _ (fun _ => congrArg J c₂.symm)).trans r₃
      rw [Category.id_comp, Category.id_comp] at e₂
      exact e₂.trans (congrArg₂ (· * ·) (congrArg (· ^ _) v₁) (congrArg (· ^ (-1 : ℤ)) v₂)))
  refine not_vanish I'.G.G I'.G.semi I'.θ I'.θgen hN fun x hx ν' hν' => ?_
  rw [← hFF] at hν'
  obtain ⟨ν, hν⟩ := exists_chart I.G.PP.isLB (F'.left x)
  obtain ⟨B, hB⟩ := hB ν' ν
  have l₂ : F.left ⁻¹ᵁ I'.G.PP.L.U ν' ⊓ I.G.PP.L.U ν ≤
      LB.wchart I.G.PP.L (fun _ : Fin 1 => 𝟙 I.G.G.left) fun _ => ν := fun z hz => Set.mem_iInter.2 fun _ => hz.2
  have := I.G.semi.smooth
  refine notMem_basicOpen_of_generic I.m2.cart.1 ((F.left.appLE _ _ inf_le_left).hom (I'.θ.f ν'))
    (B.val * (I.G.G.left.presheaf.map (homOfLE l₂).op).hom (σ.f fun _ => ν)) ha (fun z hz => ?_) (x := F'.left x)
    ((congrArg (fun q => q x) (Over.w F')).trans hx) ?_
  · obtain ⟨κ, hκ⟩ := exists_chart I.t'.PP.isLB z
    obtain ⟨κ', hκ'⟩ := exists_chart I'.t'.PP.isLB (ψ.left z)
    choose J hJ using fun χ : I.t'.G.left ⟶ Xo.univ.t.G.left => exists_chart Xo.univ.t.PP.isLB (χ z)
    have e₁ := hB z (J (𝟙 _ ≫ I.m1.φ)) (J ((𝟙 _ ≫ ψ.left) ≫ I'.m1.φ)) κ κ' hz (hJ _) (hJ _) hκ hκ'
    obtain ⟨τ, t₁, t₂⟩ := tie_pt I g₁ g₂ hσ (𝟙 _) z hJ ν κ hz.2 hκ
    obtain ⟨τ', u₁, u₂⟩ := theta_pt I' g₁' g₂' (𝟙 _ ≫ ψ.left) z _ ν' κ' (hJ ((𝟙 _ ≫ ψ.left) ≫ I'.m1.φ))
      ((congrArg (fun q => q z ∈ I'.G.PP.L.U ν') hψ₂).mpr hz.1) hκ'
    have c₁ : (𝟙 _ ≫ g) ≫ Ψ = (𝟙 _ ≫ ψ.left) ≫ g' := by rw [Category.assoc, hg, Category.assoc]
    have c₂ : ((𝟙 _ ≫ ψ.left) ≫ g') ≫ (snd (Over.mk (xOf y')) Xo.univ.t.G).left = (𝟙 _ ≫ ψ.left) ≫ I'.m1.φ := by
      rw [Category.assoc, g₁']
    have c₃ : ((𝟙 _ ≫ ψ.left) ≫ g') ≫ (fst (Over.mk (xOf y')) Xo.univ.t.G).left = I.t'.G.hom := by
      rw [Category.assoc, g₂', Category.id_comp, Over.w]
    have e₂ := hcar.val (𝟙 _ ≫ g) z hJ
    have e₃ := sv_smul (T := Over.mk (xOf y')) (a := toΓ _ a) hs'' ((𝟙 _ ≫ ψ.left) ≫ g') z hJ
    have e₄ := (sval_of (φ := fun _ : Fin 1 => (snd (Over.mk (xOf y')) Xo.univ.t.G).left) (ε := fun _ => 1) y'.1.s
      ((𝟙 _ ≫ ψ.left) ≫ g') z J _ (fun _ => congrArg J c₂)).trans u₁
    rw [c₃] at e₃
    replace e₃ := e₃.trans (congrArg₂ (· * ·) (rfl : _ = cst I.t'.G.hom z a) e₄)
    rw [c₁, e₃, t₁, bv] at e₂
    rw [Category.assoc, hψ₂, Category.id_comp (I.m2.φ ≫ _)] at u₂
    rw [Category.id_comp I.m2.φ] at t₂
    exact (congrArg₂ (· * ·) rfl ((gs_appLE _ _ _ _ _ z hz _).trans u₂)).trans ((units_mul_relation_rearrange_commRing e₂).trans
      ((gs_mul _ z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_unit _ z _ hz _).trans (congrArg Units.val e₁))
        ((gs_res _ z l₂ hz _).trans t₂))).symm)
  · rw [Scheme.basicOpen_appLE]
    exact ⟨⟨I'.G.G.left.basicOpen_le _ hν', hν⟩, hν'⟩

end GlobalTheory.HkIntegral.PullScalar
