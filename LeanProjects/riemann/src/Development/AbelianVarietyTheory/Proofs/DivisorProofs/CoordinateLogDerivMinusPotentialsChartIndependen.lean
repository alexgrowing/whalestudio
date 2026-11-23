import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerField
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatConn
open GlobalTheory.KS.DlogPol (gs_rsT gs_pbT gs_one gs_sub)

theorem cancel_unit {A B : Type} [CommRing A] [CommRing B] (π : A →+* B) (δ : A → B) (u : Aˣ) (L Δ : B)
    (h₁ : δ u.val = π u.val * L) (h₂ : δ u.val = π u.val * Δ) : L = Δ :=
  ((Units.isUnit u).map π).mul_left_cancel (h₁.symm.trans h₂)

section ChartFreeProof

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} {Y : Ray oa} {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} {h : Heat Y.H Y.q.left Q.P.L dd D}
  {K : Type} [Field K] {ν : R} {A₀ : Over (Sp K)} {m₀ : A₀.left ⟶ Q.P.A.left} {V : h.J → Q.P.A.left.Opens}
  {ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)} {pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)}

theorem dE_trans_unit {D' : R → K} (hC : IsConnK Q.P.A Q.P.L A₀ m₀ D' V h.j ed pb) (hD : IsDesc Y h ν m₀ V ed pb)
    (hCo : Commutes Q m₀ ed) (α : Q.X) (j : Fin 4) (T : A₀.left ⟶ A₀.left) (h₁ : T ≫ m₀ = m₀ ≫ Q.famφB α j)
    (h₂ : T ≫ A₀.hom = A₀.hom) {Z : Scheme.{0}} {a : Z ⟶ Y.H.left} {b : Z ⟶ A₀.left} (w : a ≫ Y.q.left = b ≫ m₀)
    (z : Z) (i₀ : h.J) (hi₀ : (b ≫ m₀) z ∈ V i₀)
    (δ : Y.H.left.presheaf.stalk (a z) → Z.presheaf.stalk z)
    (hδ : ∀ W, W ≤ h.W i₀ → a z ∈ W → ∀ f, δ (gs (𝟙 _) (a z) W f) = gs a z W (dE h ν i₀ W f))
    (c c' : h.J) (hc : (b ≫ T ≫ m₀) z ∈ V c) (hc' : (b ≫ T ≫ m₀) z ∈ V c') :
    δ (gs (Y.q.left ≫ Q.famφB α j) (a z) (Q.P.L.U (h.j c) ⊓ Q.P.L.U (h.j c')) (Q.P.L.g (h.j c) (h.j c')).val) =
      (a.stalkMap z).hom (gs (Y.q.left ≫ Q.famφB α j) (a z) (Q.P.L.U (h.j c) ⊓ Q.P.L.U (h.j c'))
        (Q.P.L.g (h.j c) (h.j c')).val) *
        (gs (b ≫ T) z (m₀ ⁻¹ᵁ V c') (pb c') - gs (b ≫ T) z (m₀ ⁻¹ᵁ V c) (pb c)) := by
  have e : a ≫ Y.q.left ≫ Q.famφB α j = b ≫ T ≫ m₀ := by rw [h₁, reassoc_of% w]
  have hVL : V c ⊓ V c' ≤ Q.P.L.U (h.j c) ⊓ Q.P.L.U (h.j c') := inf_le_inf (hC.2.2.1 c) (hC.2.2.1 c')
  have hpV : (Q.famφB α j) (Y.q.left (a z)) ∈ V c ⊓ V c' := by
    show (a ≫ Y.q.left ≫ Q.famφB α j) z ∈ V c ⊓ V c'
    rw [e]; exact ⟨hc, hc'⟩
  have hq0 : Y.q.left (a z) ∈ V i₀ := by
    show (a ≫ Y.q.left) z ∈ V i₀
    rw [w]; exact hi₀
  have hqU : Y.q.left (a z) ∈ V i₀ ⊓ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c') := ⟨hq0, hpV⟩
  have hbU : (b ≫ m₀) z ∈ V i₀ ⊓ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c') := by
    show (b ≫ m₀) z ∈ _
    rw [← w]; exact hqU
  set g := (Q.P.L.g (h.j c) (h.j c')).val
  set F := ((Q.famφB α j).app (V c ⊓ V c')).hom (rsT g (V c ⊓ V c'))
  set f := resG Q.P.A.left (inf_le_right : V i₀ ⊓ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c') ≤ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c')) F
  have s₁ : gs (Y.q.left ≫ Q.famφB α j) (a z) (Q.P.L.U (h.j c) ⊓ Q.P.L.U (h.j c')) g =
      gs (𝟙 _) (a z) (Y.q.left ⁻¹ᵁ (V i₀ ⊓ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c'))) ((Y.q.left.app _).hom f) := by
    rw [gs_pull (𝟙 _) Y.q.left (a z) _ hqU f, Category.id_comp, gs_res Y.q.left (a z) inf_le_right hqU F,
      gs_pull Y.q.left (Q.famφB α j) (a z) _ hpV _, gs_rsT (Y.q.left ≫ Q.famφB α j) (a z) hVL hpV]
  have hle : Y.q.left ⁻¹ᵁ (V i₀ ⊓ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c')) ≤ h.W i₀ := by
    rw [hD.1 i₀]; exact fun _ hx ↦ hx.1
  have hbT : (b ≫ T) z ∈ m₀ ⁻¹ᵁ (V c ⊓ V c') := ⟨hc, hc'⟩
  have m : (Y.q.left ≫ Q.famφB α j) (a z) ∈ Q.P.L.U (h.j c) ⊓ Q.P.L.U (h.j c') := hVL hpV
  have hπ : (a.stalkMap z).hom (gs (Y.q.left ≫ Q.famφB α j) (a z) _ g) = gs (b ≫ T ≫ m₀) z _ g := by
    rw [← e, ← gs_pull a (Y.q.left ≫ Q.famφB α j) z _ m g, gs_stalkMap a z _ m, gs_pull (𝟙 _) _ (a z) _ m g,
      Category.id_comp]
  rw [hπ, s₁, hδ _ hle hqU, ← hD.2.1 Z a b w z i₀ _ inf_le_left hbU f,
    hC.1.res _ _ inf_le_right le_top F, gs_rsT b z (show m₀ ⁻¹ᵁ (V i₀ ⊓ Q.famφB α j ⁻¹ᵁ (V c ⊓ V c')) ≤ m₀ ⁻¹ᵁ (Q.famφB α j ⁻¹ᵁ (V c ⊓ V c')) from fun _ hx ↦ hx.2) hbU,
    hCo α j T h₁ h₂ (V c ⊓ V c') (rsT g (V c ⊓ V c')) Z b z ⟨hc, hc'⟩, hC.2.2.2 c c',
    gs_mul _ z _ hbT, gs_sub _ z _ hbT, gs_rsT (b ≫ T) z (show m₀ ⁻¹ᵁ (V c ⊓ V c') ≤ m₀ ⁻¹ᵁ V c' from fun _ hx ↦ hx.2) hbT, gs_rsT (b ≫ T) z (show m₀ ⁻¹ᵁ (V c ⊓ V c') ≤ m₀ ⁻¹ᵁ V c from fun _ hx ↦ hx.1) hbT,
    gs_pbT (b ≫ T) m₀ z (fun _ hx ↦ hVL hx) hbT, Category.assoc]

end ChartFreeProof

theorem chartFree : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsFibre Y h φ e ν A₀ m₀ → ∀ (V : h.J → Q.P.A.left.Opens) (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), IsConnK Q.P.A Q.P.L A₀ m₀ (fun r => φ (D r)) V h.j ed pb → IsDesc Y h ν m₀ V ed pb → Commutes Q m₀ ed → ∀ α : Q.X, ChartFree Y h ν m₀ V pb α := by
  intro R _ _ Q O _ _ _ oa Y n dd D h K _ _ φ e ν A₀ _ m₀ hF V ed pb hC hD hCo α T h₁ h₂ Z a b hw z i i' hi hi' w H
  unfold CoordAt at H ⊢
  have hV : ∀ c, V c ≤ Q.P.L.U (h.j c) := hC.2.2.1
  have hm := hF.mem_chart hD hV h₁ hw hi
  have hm' := hF.mem_chart hD hV h₁ hw hi'
  have hT0 := hF.T_zero (h₁ 0) (h₂ 0)
  have hi₀ : (b ≫ m₀) z ∈ V (i 0) := by
    have := hi 0
    rwa [hT0, Category.id_comp] at this
  obtain ⟨δ, -, hδm, hδ⟩ := exists_stalkDer_field (isField_dE h ν hF.field (i 0)) a z hm.1
  obtain ⟨l, hl⟩ := exists_dlog (a.stalkMap z).hom δ hδm
  have hx : gs a z (h.W (i 0) ⊓ xU Y α fun j ↦ h.j (i j))
      (dE h ν (i 0) _ (rsT (xc Y α fun j ↦ h.j (i j)).val (h.W (i 0) ⊓ xU Y α fun j ↦ h.j (i j)))) =
      δ (gm (𝟙 _) (a z) (xU Y α fun j ↦ h.j (i j)) (xc Y α fun j ↦ h.j (i j))).val := by
    rw [← hδ _ inf_le_left hm, gs_rsT (𝟙 _) (a z) inf_le_right hm, gs_unit (𝟙 _) (a z) _ hm.2]
  have hx' : gs a z (h.W (i' 0) ⊓ xU Y α fun j ↦ h.j (i' j))
      (dE h ν (i' 0) _ (rsT (xc Y α fun j ↦ h.j (i' j)).val (h.W (i' 0) ⊓ xU Y α fun j ↦ h.j (i' j)))) =
      δ (gm (𝟙 _) (a z) (xU Y α fun j ↦ h.j (i' j)) (xc Y α fun j ↦ h.j (i' j))).val := by
    have hU : a z ∈ h.W (i 0) ⊓ h.W (i' 0) ⊓ xU Y α fun j ↦ h.j (i' j) := ⟨⟨hm.1, hm'.1⟩, hm'.2⟩
    have hle : h.W (i 0) ⊓ h.W (i' 0) ⊓ (xU Y α fun j ↦ h.j (i' j)) ≤ h.W (i' 0) ⊓ xU Y α fun j ↦ h.j (i' j) :=
      fun _ hy ↦ ⟨hy.1.2, hy.2⟩
    rw [← gs_res a z hle hU, ← (isField_dE h ν hF.field (i' 0)).2.2 _ _ hle inf_le_left,
      ← hF.dE_agree hw z (i 0) (i' 0) _ inf_le_left hU, ← hδ _ (inf_le_left.trans inf_le_left) hU, gs_res (𝟙 _) (a z) hle hU,
      gs_rsT (𝟙 _) (a z) inf_le_right hm', gs_unit (𝟙 _) (a z) _ hm'.2]
  have ht := gen_trans ((Y.Φ Y.H (𝟙 _)).isGen α) (𝟙 Y.H.left) (a z) hm.2 hm'.2
  have hu : ∀ k, (l (gm (𝟙 Y.H.left ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k) (a z)
      (Q.P.L.U (h.j (i (![1, 2, 0, 3] k))) ⊓ Q.P.L.U (h.j (i' (![1, 2, 0, 3] k))))
      (Q.P.L.g (h.j (i (![1, 2, 0, 3] k))) (h.j (i' (![1, 2, 0, 3] k)))))).toAdd =
      gs (b ≫ T (![1, 2, 0, 3] k)) z (m₀ ⁻¹ᵁ V (i' (![1, 2, 0, 3] k))) (pb (i' (![1, 2, 0, 3] k))) -
      gs (b ≫ T (![1, 2, 0, 3] k)) z (m₀ ⁻¹ᵁ V (i (![1, 2, 0, 3] k))) (pb (i (![1, 2, 0, 3] k))) := by
    intro k
    have mem : (𝟙 Y.H.left ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k) (a z) ∈
        Q.P.L.U (h.j (i (![1, 2, 0, 3] k))) ⊓ Q.P.L.U (h.j (i' (![1, 2, 0, 3] k))) :=
      ⟨Set.mem_iInter.1 hm.2 k, Set.mem_iInter.1 hm'.2 k⟩
    refine cancel_unit _ δ _ _ _ (hl _) ?_
    rw [← gs_unit _ _ _ mem, Category.id_comp, gtφT_eq]
    exact dE_trans_unit hC hD hCo α _ (T _) (h₁ _) (h₂ _) hw z (i 0) hi₀ δ hδ _ _ (hi _) (hi' _)
  have e2 := congrArg (fun u ↦ (l u).toAdd) ht
  simp only [map_mul, toAdd_mul, trF, map_prod, map_zpow, toAdd_prod, toAdd_zpow, Fin.sum_univ_four] at e2
  rw [hu 0, hu 1, hu 2, hu 3] at e2
  simp only [DegPre.gtε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, neg_smul, one_smul, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at e2
  rw [hx, gs_stalkMap a z _ hm.2, gs_unit (𝟙 _) (a z) _ hm.2] at H
  have eH := cancel_unit _ δ _ _ _ (hl _) H
  rw [hx', hl, gs_stalkMap a z _ hm'.2, gs_unit (𝟙 _) (a z) _ hm'.2]
  congr 1
  linear_combination eH - e2

end GlobalTheory.HeatConn
