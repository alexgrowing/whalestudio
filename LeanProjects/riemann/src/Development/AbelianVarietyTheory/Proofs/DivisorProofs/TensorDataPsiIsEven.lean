import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensEven

open TopologicalSpace

section Gen

variable {X X' Y Y₀ : Scheme.{0}} {M : LB X} {M' : LB X'} {P : Type} [Fintype P] {pr : P → (X' ⟶ X)} {εp : P → ℤ}

def bwE (w : LB.Iso M' (LB.LinComb M pr εp)) {Z : Scheme.{0}} (ψ : Z ⟶ X') (z : Z) (jN : P → M.ι) (k : M'.ι) :
    (Z.presheaf.stalk z)ˣ := gm ψ z (LB.wchart M pr jN ⊓ M'.U k) (w.s (jN, k))

theorem bwE_trans {Z : Scheme.{0}} (w : LB.Iso M' (LB.LinComb M pr εp)) (hw : w.IsGen) (ψ : Z ⟶ X') (z : Z)
    {jN jN' : P → M.ι} {k k' : M'.ι} (h₁ : ψ z ∈ LB.wchart M pr jN) (h₁' : ψ z ∈ LB.wchart M pr jN')
    (h₂ : ψ z ∈ M'.U k) (h₂' : ψ z ∈ M'.U k') :
    bwE w ψ z jN k = (∏ i, gm (ψ ≫ pr i) z (M.U (jN i) ⊓ M.U (jN' i)) (M.g (jN i) (jN' i)) ^ εp i) *
      (gm ψ z (M'.U k ⊓ M'.U k') (M'.g k k'))⁻¹ * bwE w ψ z jN' k' := by
  have hm : ψ z ∈ LB.wchart M pr jN ⊓ M'.U k ⊓ (LB.wchart M pr jN' ⊓ M'.U k') := ⟨⟨h₁, h₂⟩, h₁', h₂'⟩
  have e := congrArg (gm ψ z (LB.wchart M pr jN ⊓ M'.U k ⊓ (LB.wchart M pr jN' ⊓ M'.U k'))) (hw (jN, k) (jN', k'))
  have d := gm_div M' (LB.LinComb M pr εp) ψ z (jN, k) (jN', k') hm
  have l := gm_linComb M pr εp ψ z jN jN' h₁ h₁'
  refine (gm_res ψ z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (d.trans (congrArg₂ (· * ·) l rfl)) (gm_res ψ z _ hm _))))

theorem gm_linCombIsoE (w : LB.Iso M' (LB.LinComb M pr εp)) {K : Type} [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (jN : K → P → M.ι) (jM : K → M'.ι)
    (hz : r z ∈ LB.wchart (LB.LinComb M pr εp) φ jN ⊓ LB.wchart M' φ jM) :
    gm r z (LB.wchart (LB.LinComb M pr εp) φ jN ⊓ LB.wchart M' φ jM) ((LB.linCombIso w φ ε).s (jN, jM)) =
      ∏ a, bwE w (r ≫ φ a) z (jN a) (jM a) ^ ε a :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun a _ => (map_zpow _ _ _).trans (congrArg (· ^ ε a)
    ((gm_res r z _ hz _).trans (gm_pull r (φ a) z (LB.wchart M pr (jN a) ⊓ M'.U (jM a))
      ⟨Set.mem_iInter.1 hz.1 a, Set.mem_iInter.1 hz.2 a⟩ _))))

variable {K : Type} [Fintype K]

def ratioE (w : LB.Iso M' (LB.LinComb M pr εp)) {φ' : K → (Y ⟶ X')} {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ}
    (ρ : P → (Y ⟶ Y₀)) (t' : LB.Gen (LB.LinComb M' φ' ε)) (t : LB.Gen (LB.LinComb M φ ε))
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (jN : K → P → M.ι) (jM : K → M'.ι) : (Z.presheaf.stalk z)ˣ :=
  (∏ a, bwE w (r ≫ φ' a) z (jN a) (jM a) ^ ε a) * gm r z (LB.wchart M' φ' jM) (t'.s jM) *
    (∏ i, gm (r ≫ ρ i) z (LB.wchart M φ (fun a => jN a i)) (t.s (fun a => jN a i)) ^ εp i)⁻¹

theorem chart_leE {φ' : K → (Y ⟶ X')} {φ : K → (Y₀ ⟶ X)} {ρ : P → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ a) (jN : K → P → M.ι) (i : P) :
    LB.wchart (LB.LinComb M pr εp) φ' jN ≤ ρ i ⁻¹ᵁ LB.wchart M φ (fun a => jN a i) := fun y hy =>
  Set.mem_iInter.2 fun a => (congrArg (fun g : Y ⟶ X => g y ∈ M.U (jN a i)) (hψ i a)).mp
    (Set.mem_iInter.1 (Set.mem_iInter.1 hy a) i)

theorem ratioE_trans (w : LB.Iso M' (LB.LinComb M pr εp)) (hw : w.IsGen) {φ' : K → (Y ⟶ X')}
    {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : P → (Y ⟶ Y₀)} (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ a)
    {t' : LB.Gen (LB.LinComb M' φ' ε)} (ht' : t'.IsGen) {t : LB.Gen (LB.LinComb M φ ε)} (ht : t.IsGen)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {jN jN' : K → P → M.ι} {jM jM' : K → M'.ι}
    (h : r z ∈ LB.wchart (LB.LinComb M pr εp) φ' jN ⊓ LB.wchart M' φ' jM)
    (h' : r z ∈ LB.wchart (LB.LinComb M pr εp) φ' jN' ⊓ LB.wchart M' φ' jM') :
    ratioE w ρ t' t r z jN jM = ratioE w ρ t' t r z jN' jM' := by
  have e₁ : ∀ a, bwE w (r ≫ φ' a) z (jN a) (jM a) = _ := fun a => bwE_trans w hw (r ≫ φ' a) z (jN' := jN' a)
    (k' := jM' a) (Set.mem_iInter.1 h.1 a) (Set.mem_iInter.1 h'.1 a) (Set.mem_iInter.1 h.2 a) (Set.mem_iInter.1 h'.2 a)
  have e₂ := gen_trans ht' r z h.2 h'.2
  have e₃ : ∀ i, gm (r ≫ ρ i) z (LB.wchart M φ (fun a => jN a i)) (t.s (fun a => jN a i)) = _ := fun i =>
    gen_trans ht (r ≫ ρ i) z (j' := fun a => jN' a i) (chart_leE hψ jN i h.1) (chart_leE hψ jN' i h'.1)
  have e₄ : ∏ i, trF (L := M) φ ε (r ≫ ρ i) z (fun a => jN a i) (fun a => jN' a i) ^ εp i =
      ∏ a, (∏ i, gm ((r ≫ φ' a) ≫ pr i) z (M.U (jN a i) ⊓ M.U (jN' a i)) (M.g (jN a i) (jN' a i)) ^ εp i) ^ ε a := by
    unfold trF
    simp_rw [← Finset.prod_zpow]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun i _ => ?_
    rw [Category.assoc, Category.assoc, hψ, ← zpow_mul, ← zpow_mul, mul_comm]
  unfold ratioE
  rw [Finset.prod_congr rfl fun a _ => congrArg (· ^ ε a) (e₁ a), e₂,
    Finset.prod_congr rfl fun i _ => congrArg (· ^ εp i) (e₃ i)]
  simp only [mul_zpow, Finset.prod_mul_distrib] at e₄ ⊢
  rw [e₄]
  simp only [inv_zpow, Finset.prod_inv_distrib, trF]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_ratioE (w : LB.Iso M' (LB.LinComb M pr εp)) {φ' : K → (Y ⟶ X')}
    {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : P → (Y ⟶ Y₀)} (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ a)
    (t' : LB.Gen (LB.LinComb M' φ' ε)) (t : LB.Gen (LB.LinComb M φ ε)) (jN : K → P → M.ι) (jM : K → M'.ι) :
    ∃ u : Γ(Y, LB.wchart (LB.LinComb M pr εp) φ' jN ⊓ LB.wchart M' φ' jM)ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z),
        r z ∈ LB.wchart (LB.LinComb M pr εp) φ' jN ⊓ LB.wchart M' φ' jM →
        gm r z _ u = ratioE w ρ t' t r z jN jM := by
  refine ⟨@id (Γ(Y, LB.wchart (LB.LinComb M pr εp) φ' jN ⊓ LB.wchart M' φ' jM)ˣ)
      ((LB.linCombIso w φ' ε).s (jN, jM)) * res inf_le_right (t'.s jM) *
      (∏ i, res (inf_le_left.trans (chart_leE hψ jN i)) (pullU (ρ i) _ (t.s (fun a => jN a i))) ^ εp i)⁻¹,
    fun Z r z hz => ?_⟩
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_linCombIsoE w φ' ε r z jN jM hz) (gm_res r z _ hz _))) ((map_inv _ _).trans (congrArg (·⁻¹)
      ((map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ => ?_)))))
  exact (map_zpow _ _ _).trans (congrArg (· ^ εp i)
    ((gm_res r z _ hz _).trans (gm_pull r (ρ i) z _ (chart_leE hψ jN i hz.1) _)))

theorem box_uniqueE {S₀ : Scheme.{0}} (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (LB.LinComb M pr εp))
    (hw : w.IsGen) {φ' : K → (Y ⟶ X')} {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : P → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ a)
    {t' : LB.Gen (LB.LinComb M' φ' ε)} (ht' : t'.IsGen) {t : LB.Gen (LB.LinComb M φ ε)} (ht : t.IsGen)
    (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    (h : ∀ y J J', Good M y J → Good M' y J' →
      (∏ a, bwE w (e ≫ φ' a) y (fun i => J ((e ≫ φ' a) ≫ pr i)) (J' (e ≫ φ' a)) ^ ε a) * val t' e y J' =
        ∏ i, val t (e ≫ ρ i) y J ^ εp i)
    (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J J') (hJ : Good M z J) (hJ' : Good M' z J') :
    (∏ a, bwE w (r ≫ φ' a) z (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a) * val t' r z J' =
      ∏ i, val t (r ≫ ρ i) z J ^ εp i := by
  choose u hu using fun q : (K → P → M.ι) × (K → M'.ι) => exists_ratioE w hψ t' t q.1 q.2
  obtain ⟨s, hs⟩ := glue_unit (⊤ : Y.Opens)
    (fun q : (K → P → M.ι) × (K → M'.ι) =>
      LB.wchart (LB.LinComb M pr εp) φ' q.1 ⊓ LB.wchart M' φ' q.2) (fun _ => le_top)
    (fun y _ => by
      choose a ha using fun k i => exists_chart hM (pr i (φ' k y))
      choose b hb using fun k => exists_chart hM' (φ' k y)
      exact Opens.mem_iSup.2 ⟨(a, b), Set.mem_iInter.2 fun k => Set.mem_iInter.2 (ha k), Set.mem_iInter.2 hb⟩) u
    (fun q q' y hy => (hu q _ (𝟙 Y) y hy.1).trans ((ratioE_trans w hw hψ ht' ht (𝟙 Y) y hy.1 hy.2).trans
      (hu q' _ (𝟙 Y) y hy.2).symm))
  obtain ⟨a, ha⟩ := hp s.val
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J J'), Good M z J → Good M' z J' →
      ((∏ a, bwE w (r ≫ φ' a) z (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a) * val t' r z J' *
        (∏ i, val t (r ≫ ρ i) z J ^ εp i)⁻¹).val = gs (r ≫ p) z ⊤ a := by
    intro Z r z J J' hJ hJ'
    have hm : r z ∈ LB.wchart (LB.LinComb M pr εp) φ' (fun a i => J ((r ≫ φ' a) ≫ pr i)) ⊓
        LB.wchart M' φ' (fun a => J' (r ≫ φ' a)) :=
      ⟨Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun i => hJ ((r ≫ φ' a) ≫ pr i), hJ'.mem _ r⟩
    have v : ∏ i, val t (r ≫ ρ i) z J ^ εp i = ∏ i, gm (r ≫ ρ i) z (LB.wchart M φ (fun a => J ((r ≫ φ' a) ≫ pr i)))
        (t.s (fun a => J ((r ≫ φ' a) ≫ pr i))) ^ εp i := Finset.prod_congr rfl fun i _ =>
      congrArg (· ^ εp i) (val_of t _ z J _ (fun a => by rw [Category.assoc, Category.assoc, hψ]))
    rw [v]
    have w₁ := (hu (fun a i => J ((r ≫ φ' a) ≫ pr i), fun a => J' (r ≫ φ' a)) Z r z hm).symm.trans
      ((congrArg (gm r z _) (hs _).symm).trans (gm_res r z le_top hm s))
    exact (congrArg Units.val w₁).trans ((gs_unit r z ⊤ trivial _).symm.trans
      ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a)))
  have a1 : a = 1 := fn_ext fun y _ => by
    choose I hI using fun χ : S₀ ⟶ X => exists_chart hM (χ y)
    choose I' hI' using fun χ : S₀ ⟶ X' => exists_chart hM' (χ y)
    have := key _ e y I I' hI hI'
    rw [h y I I' hI hI', mul_inv_cancel, he] at this
    rw [← this, gs_eq _ y ⊤ trivial, map_one, map_one, Units.val_one]
  have := key Z r z J J' hJ hJ'
  rw [a1, gs_eq _ z ⊤ trivial, map_one, map_one] at this
  exact mul_inv_eq_one.1 (Units.ext this)

end Gen

section Tens

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem inv_tensφ (T : Tens D D' W) (k : (Fin r × Fin r) × Fin 4) :
    (ι[D'.P.A]).left ≫ tensφ T.pr k = tensφ T.pr k ≫ (ι[D.P.A]).left := by
  have h : ∀ f : D'.P.A ⟶ D.P.A, ι[D'.P.A] ≫ f = f⁻¹ → (ι[D'.P.A]).left ≫ f.left = f.left ≫ (ι[D.P.A]).left :=
    fun f hf => by rw [← Over.comp_left, hf, Hom.inv_def, Over.comp_left]
  have e : ι[D'.P.A] = (𝟙 D'.P.A)⁻¹ := by rw [Hom.inv_def, Category.id_comp]
  have hi : ∀ i, ι[D'.P.A] ≫ T.pr i = (T.pr i)⁻¹ := fun i => by
    have := T.pr_hom i
    rw [e, GrpObj.inv_comp, Category.id_comp]
  obtain ⟨⟨i, j⟩, m⟩ := k
  fin_cases m
  · exact h (T.pr i * T.pr j) (by rw [MonObj.comp_mul, hi, hi, mul_inv])
  · exact h _ (hi i)
  · exact h _ (hi j)
  · exact h (1 : D'.P.A ⟶ D.P.A) (by rw [MonObj.comp_one, inv_one])

theorem one_tensφ (T : Tens D D' W) (k : (Fin r × Fin r) × Fin 4) : eSec D'.P.A ≫ tensφ T.pr k = eSec D.P.A := by
  have h1 : (η[D.P.A] : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) = 1 := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have h : ∀ f : D'.P.A ⟶ D.P.A, η[D'.P.A] ≫ f = 1 → eSec D'.P.A ≫ f.left = eSec D.P.A := fun f hf => by
    show η[D'.P.A].left ≫ f.left = η[D.P.A].left
    rw [← Over.comp_left, hf, h1]
  have hi : ∀ i, η[D'.P.A] ≫ T.pr i = 1 := fun i => by
    have := T.pr_hom i
    rw [IsMonHom.one_hom, h1]
  obtain ⟨⟨i, j⟩, m⟩ := k
  fin_cases m
  · exact h (T.pr i * T.pr j) (by rw [MonObj.comp_mul, hi, hi, _root_.mul_one])
  · exact h _ (hi i)
  · exact h _ (hi j)
  · exact h (1 : D'.P.A ⟶ D.P.A) (MonObj.comp_one _)

theorem sym_tens (hG : GlobalFnsSt) (T : Tens D D' W) {Z : Scheme.{0}} (q : Z ⟶ D'.P.A.left) (y : Z) {J J'}
    (hJ : Good D.P.L y J) (hJ' : Good D'.P.L y J') :
    bwE T.w (q ≫ (ι[D'.P.A]).left) y (fun k => J ((q ≫ (ι[D'.P.A]).left) ≫ tensφ T.pr k))
        (J' (q ≫ (ι[D'.P.A]).left)) *
      (bwE T.w q y (fun k => J (q ≫ tensφ T.pr k)) (J' q))⁻¹ * val D'.sym q y J' =
      ∏ k, val D.sym (q ≫ tensφ T.pr k) y J ^ tensε W k := by
  have p : ∀ {Z : Scheme.{0}} (r : Z ⟶ D'.P.A.left) {U : Type} [CommGroup U] (f : (Z ⟶ D'.P.A.left) → U),
      ∏ a : Fin 2, f (r ≫ (![(ι[D'.P.A]).left, 𝟙 D'.P.A.left] : Fin 2 → (D'.P.A.left ⟶ D'.P.A.left)) a) ^
        (![1, -1] : Fin 2 → ℤ) a = f (r ≫ (ι[D'.P.A]).left) * (f r)⁻¹ := fun r U _ f => by
    simp [Fin.prod_univ_two]
  have hψ : ∀ k (a : Fin 2), (![(ι[D'.P.A]).left, 𝟙 D'.P.A.left] : Fin 2 → (D'.P.A.left ⟶ D'.P.A.left)) a ≫
      tensφ T.pr k = tensφ T.pr k ≫ (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → (D.P.A.left ⟶ D.P.A.left)) a :=
    fun k a => by
      fin_cases a
      · exact inv_tensφ T k
      · simp
  have key := box_uniqueE (pr := tensφ T.pr) (εp := tensε W) D.P.isLB D'.P.isLB T.w T.w_gen (ρ := tensφ T.pr) hψ
    D'.sym_gen D.sym_gen D'.P.A.hom (eSec D'.P.A) (Over.w η[D'.P.A]) (hG _ _ D'.P.isAb).2
    (fun s I I' hI hI' => by
      have q := p (Z := Spec (CommRingCat.of R)) (eSec D'.P.A) (fun ψ => bwE T.w ψ s (fun i => I (ψ ≫ tensφ T.pr i)) (I' ψ))
      have o : eSec D'.P.A ≫ (ι[D'.P.A]).left = eSec D'.P.A :=
        congrArg (fun m => m.left) (GrpObj.one_inv : η[D'.P.A] ≫ ι[D'.P.A] = η[D'.P.A])
      rw [o, mul_inv_cancel] at q
      have v' := val_corr hI' D'.sym_rig (𝟙 _)
      rw [val_pull hI', Category.id_comp, val_one] at v'
      have v := val_corr hI D.sym_rig (𝟙 _)
      rw [val_pull hI, Category.id_comp, val_one] at v
      refine (congrArg₂ (· * ·) q v').trans (Eq.trans (by simp) (Finset.prod_eq_one fun k _ => ?_).symm)
      rw [one_tensφ T k, v, one_zpow]) _ q y J J' hJ hJ'
  exact (congrArg₂ (· * ·) (p q (fun ψ => bwE T.w ψ y (fun i => J (ψ ≫ tensφ T.pr i)) (J' ψ))) rfl).symm.trans key

end Tens

section Main

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}

theorem pt_of (x : D'.X) (f : D'.P.A ⟶ D.P.A) (a : D.X)
    (hf : (toUnit (TK R) ≫ D'.c x) ≫ f = toUnit (TK R) ≫ D.c a) : D'.xK x ≫ f.left = D.xK a := by
  show (toUnit (TK R) ≫ D'.c x).left ≫ f.left = (toUnit (TK R) ≫ D.c a).left
  rw [← Over.comp_left, hf]

theorem cp (T : Tens D D' W) (x : D'.X) (i : Fin r) :
    (toUnit (TK R) ≫ D'.c x) ≫ T.pr i = toUnit (TK R) ≫ D.c (T.xe x i) := by
  rw [Category.assoc, T.c_pr]

theorem pt_pr (T : Tens D D' W) (x : D'.X) (i : Fin r) : D'.xK x ≫ (T.pr i).left = D.xK (T.xe x i) :=
  pt_of x _ _ (cp T x i)

theorem pt_mul (T : Tens D D' W) (x : D'.X) (i j : Fin r) :
    D'.xK x ≫ (T.pr i * T.pr j).left = D.xK (T.xe x i + T.xe x j) :=
  pt_of x _ _ (by rw [MonObj.comp_mul, cp, cp, ← MonObj.comp_mul]; exact congrArg _ (D.c_add _ _).symm)

theorem pt_one (x : D'.X) : D'.xK x ≫ (1 : D'.P.A ⟶ D.P.A).left = D.xK 0 := by
  have c0 : D.c 0 = 1 := mul_eq_left.1 ((D.c_add 0 0).symm.trans (congrArg D.c (add_zero 0)))
  exact pt_of x _ _ (by rw [MonObj.comp_one, c0, MonObj.comp_one])

theorem alg {U : Type} [CommGroup U] (A B S Pm Pp Q : U) (h₁ : A * B⁻¹ * S = Q) (h₂ : Pm * Q = Pp) :
    A * Pm * S = B * Pp := by
  subst h₁ h₂
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Main

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (D : DegData R (maximalIdeal R)) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ),
    Tens D.toPre D' W → D'.PsiEven := by
  intro R _ _ _ _ D D' r W T x
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  choose J hJ using fun ψ : (TK R).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
  have hJ : Good D.toPre.P.L y J := hJ
  rw [val_mul hJ', val_pull hJ', Category.id_comp]
  have key := sym_tens GlobalTheory.globalFns_holds T (D'.xK x) y hJ hJ'
  have b₁ := T.psi x y J J' hJ hJ'
  have b₂ := T.psi (-x) y J J' hJ hJ'
  have n : D'.xK (-x) = D'.xK x ≫ (ι[D'.P.A]).left := by
    show (toUnit (TK R) ≫ D'.c (-x)).left = _
    rw [GlobalTheory.PsiEvenPull.c_neg, ← Category.assoc, Over.comp_left]
  rw [← n] at key
  have ev : ∀ c, val (D.toPre.psi (-c)) (𝟙 _) y J * val D.toPre.sym (D.toPre.xK c) y J =
      val (D.toPre.psi c) (𝟙 _) y J := fun c => by
    have := val_corr hJ (D.psi_even c) (𝟙 _)
    rwa [val_mul hJ, val_pull hJ, Category.id_comp] at this
  have s0 : val D.toPre.sym (D.toPre.xK 0) y J = 1 := by
    have := ev 0
    rw [neg_zero] at this
    exact mul_eq_left.1 this
  have tv : ∀ a b, val (D.toPre.tau a b) (𝟙 _) y J = val (D.toPre.psi (a + b)) (𝟙 _) y J *
      (val (D.toPre.psi a) (𝟙 _) y J)⁻¹ * (val (D.toPre.psi b) (𝟙 _) y J)⁻¹ * (val D.toPre.rigK (𝟙 _) y J)⁻¹ :=
    fun a b => by
      unfold DegPre.tau
      rw [val_mul hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_inv]
  have term : ∀ i j, val (D.toPre.tau (T.xe (-x) i) (T.xe (-x) j)) (𝟙 _) y J *
      ∏ m : Fin 4, val D.toPre.sym (D'.xK x ≫ tensφ T.pr ((i, j), m)) y J ^ Oε m =
      val (D.toPre.tau (T.xe x i) (T.xe x j)) (𝟙 _) y J := fun i j => by
    have hn : ∀ i, T.xe (-x) i = -T.xe x i := fun i => by rw [map_neg]; rfl
    rw [hn, hn, tv, tv, Fin.prod_univ_four]
    simp only [tensφ, GlobalTheory.PolDeg.lamPts, Oε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [pt_mul, pt_pr, pt_pr, pt_one, s0, ← neg_add, ← ev (T.xe x i + T.xe x j), ← ev (T.xe x i), ← ev (T.xe x j)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
    abel
  have Qe : ∏ k, val D.toPre.sym (D'.xK x ≫ tensφ T.pr k) y J ^ tensε W k =
      ∏ i, ∏ j, (∏ m : Fin 4, val D.toPre.sym (D'.xK x ≫ tensφ T.pr ((i, j), m)) y J ^ Oε m) ^ W i j := by
    rw [Fintype.prod_prod_type, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    rw [← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun m _ => ?_
    simp only [tensε]
    rw [mul_comm (W i j), zpow_mul]
  have E : (∏ i, ∏ j, val (D.toPre.tau (T.xe (-x) i) (T.xe (-x) j)) (𝟙 _) y J ^ W i j) *
      ∏ k, val D.toPre.sym (D'.xK x ≫ tensφ T.pr k) y J ^ tensε W k =
      ∏ i, ∏ j, val (D.toPre.tau (T.xe x i) (T.xe x j)) (𝟙 _) y J ^ W i j := by
    rw [Qe, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← mul_zpow, term]
  rw [b₁, b₂]
  exact alg _ _ _ _ _ _ key E

end GlobalTheory.TensEven
