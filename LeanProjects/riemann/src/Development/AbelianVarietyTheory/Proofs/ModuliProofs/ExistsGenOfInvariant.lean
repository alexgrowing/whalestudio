import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.IsoDescent

variable {X X' Y Y' : Scheme.{0}}

theorem exists_gen_of_invariant (M : LB Y) (m : Y' ⟶ Y) {I : Type} (t : I → (Y' ⟶ Y')) (ht : ∀ i, t i ≫ m = m)
    (hd : ∀ (U : Y.Opens) (f : Γ(Y', m ⁻¹ᵁ U)),
      (∀ i (e : m ⁻¹ᵁ U ≤ t i ⁻¹ᵁ (m ⁻¹ᵁ U)), ((t i).appLE _ _ e).hom f = f) →
      ∃! g : Γ(Y, U), (m.app U).hom g = f)
    (a : ∀ j, Γ(Y', m ⁻¹ᵁ M.U j)ˣ)
    (hc : ∀ (y : Y') i j, m y ∈ M.U i → m y ∈ M.U j →
      gm (𝟙 Y') y _ (a i) = gm m y (M.U i ⊓ M.U j) (M.g i j) * gm (𝟙 Y') y _ (a j))
    (hinv : ∀ i (y : Y') j, m y ∈ M.U j → m (t i y) ∈ M.U j → gm (t i) y _ (a j) = gm (𝟙 Y') y _ (a j)) :
    ∃ v : LB.Gen M, v.IsGen := by
  have hinj : ∀ U : Y.Opens, Function.Injective (m.app U).hom := by
    intro U g g' h
    refine (hd U ((m.app U).hom g) fun i e => fn_ext fun y hy => ?_).unique rfl h.symm
    refine (gs_res (𝟙 Y') y e hy _).trans ((gs_pull (𝟙 Y') (t i) y (m ⁻¹ᵁ U) (e hy) _).trans
      ((gs_pull (𝟙 Y' ≫ t i) m y U (e hy) _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') m y _ hy _).symm)))
    rw [Category.assoc, ht]
  have hunit : ∀ (U : Y.Opens) (a : Γ(Y', m ⁻¹ᵁ U)ˣ),
      (∀ i (e : m ⁻¹ᵁ U ≤ t i ⁻¹ᵁ (m ⁻¹ᵁ U)), res e (pullU (t i) _ a) = a) →
      ∃ b : Γ(Y, U)ˣ, pullU m U b = a := by
    intro U a ha
    obtain ⟨g, hg, -⟩ := hd U a.val fun i e => congrArg Units.val (ha i e)
    obtain ⟨g', hg', -⟩ := hd U (a⁻¹).val fun i e => congrArg Units.val
      (show res e (pullU (t i) _ a⁻¹) = a⁻¹ by rw [map_inv, map_inv, ha i e])
    have h1 : g * g' = 1 := hinj U (by rw [map_mul, map_one, hg, hg']; exact a.mul_inv)
    exact ⟨⟨g, g', h1, (mul_comm _ _).trans h1⟩, Units.ext hg⟩
  have hex : ∀ j, ∃ b : Γ(Y, M.U j)ˣ, pullU m _ b = a j := by
    intro j
    refine hunit _ _ fun i e => unit_ext fun y hy => ?_
    refine (gm_res (𝟙 Y') y e hy _).trans ((gm_pull (𝟙 Y') (t i) y (m ⁻¹ᵁ M.U j) (e hy) _).trans ?_)
    rw [Category.id_comp]
    exact hinv i y j hy (e hy)
  choose b hb using hex
  refine ⟨⟨b⟩, fun i j => Units.ext (hinj _ (congrArg Units.val
    (show pullU m _ _ = pullU m _ _ from unit_ext fun y hy => ?_)))⟩
  have val : ∀ j, y ∈ m ⁻¹ᵁ M.U j → gm (𝟙 Y' ≫ m) y _ (b j) = gm (𝟙 Y') y _ (a j) := fun j hj =>
    (gm_pull (𝟙 Y') m y _ hj _).symm.trans (congrArg _ (hb j))
  refine (gm_pull (𝟙 Y') m y _ hy _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') m y _ hy _).symm)
  refine ((gm_res _ y _ hy _).trans (val i hy.1)).trans ((hc y i j hy.1 hy.2).trans (Eq.symm ?_))
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (by rw [Category.id_comp])
    ((gm_res _ y _ hy _).trans (val j hy.2)))

variable {L : LB X} {L' : LB X'} {K K' : Type} [Fintype K] [Fintype K']

theorem lbIso_of_invariant (hL : L.IsLB) (hL' : L'.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X'))
    (ε' : K' → ℤ) (m : Y' ⟶ Y) {I : Type} (t : I → (Y' ⟶ Y')) (ht : ∀ i, t i ≫ m = m)
    (hd : ∀ (U : Y.Opens) (f : Γ(Y', m ⁻¹ᵁ U)),
      (∀ i (e : m ⁻¹ᵁ U ≤ t i ⁻¹ᵁ (m ⁻¹ᵁ U)), ((t i).appLE _ _ e).hom f = f) →
      ∃! g : Γ(Y, U), (m.app U).hom g = f)
    (u : LB.Gen (LB.LinComb L (fun k => m ≫ φ k) ε)) (hu : u.IsGen)
    (u' : LB.Gen (LB.LinComb L' (fun k => m ≫ φ' k) ε')) (hu' : u'.IsGen)
    (hinv : ∀ i y J J', Good L y J → Good L' y J' →
      val u' (t i) y J' * (val u (t i) y J)⁻¹ = val u' (𝟙 Y') y J' * (val u (𝟙 Y') y J)⁻¹) :
    LBIso (LB.LinComb L φ ε) (LB.LinComb L' φ' ε') := by
  have l₁ : ∀ p : (K' → L'.ι) × (K → L.ι), m ⁻¹ᵁ (LB.wchart L' φ' p.1 ⊓ LB.wchart L φ p.2) ≤
      LB.wchart L' (fun k => m ≫ φ' k) p.1 := fun p y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 k
  have l₂ : ∀ p : (K' → L'.ι) × (K → L.ι), m ⁻¹ᵁ (LB.wchart L' φ' p.1 ⊓ LB.wchart L φ p.2) ≤
      LB.wchart L (fun k => m ≫ φ k) p.2 := fun p y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 k
  have v : ∀ (r : Y' ⟶ Y') (y : Y') (p : (K' → L'.ι) × (K → L.ι)),
      r y ∈ m ⁻¹ᵁ (LB.wchart L' φ' p.1 ⊓ LB.wchart L φ p.2) →
      gm r y _ (res (l₁ p) (u'.s p.1) * (res (l₂ p) (u.s p.2))⁻¹) =
        gm r y (LB.wchart L' (fun k => m ≫ φ' k) p.1) (u'.s p.1) *
          (gm r y (LB.wchart L (fun k => m ≫ φ k) p.2) (u.s p.2))⁻¹ := fun r y p h =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r y _ h _)
      ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res r y _ h _))))
  refine exists_gen_of_invariant (LB.div (LB.LinComb L' φ' ε') (LB.LinComb L φ ε)) m t ht hd
    (fun p => res (l₁ p) (u'.s p.1) * (res (l₂ p) (u.s p.2))⁻¹) (fun y p q hp hq => ?_) (fun i y p hp hp' => ?_)
  · refine (v (𝟙 Y') y p hp).trans (Eq.trans ?_ (congrArg₂ (· * ·) ((gm_div _ _ m y p q ⟨hp, hq⟩).trans
      (congrArg₂ (fun a b => a * b⁻¹) (gm_linComb L' φ' ε' m y p.1 q.1 hp.1 hq.1)
        (gm_linComb L φ ε m y p.2 q.2 hp.2 hq.2))) (v (𝟙 Y') y q hq)).symm)
    rw [gen_trans hu' (𝟙 Y') y (l₁ p hp) (l₁ q hq), gen_trans hu (𝟙 Y') y (l₂ p hp) (l₂ q hq), mul_inv,
      mul_mul_mul_comm]
    simp only [trF, Category.id_comp]
  · choose J hJ using fun χ : Y' ⟶ X => exists_chart hL (χ y)
    choose J' hJ' using fun χ : Y' ⟶ X' => exists_chart hL' (χ y)
    have gJ : Good L y J := hJ
    have gJ' : Good L' y J' := hJ'
    refine (v (t i) y p hp').trans (Eq.trans ?_ (v (𝟙 Y') y p hp).symm)
    rw [gen_trans hu' (t i) y (l₁ p hp') (gJ'.mem _ _), gen_trans hu (t i) y (l₂ p hp') (gJ.mem _ _),
      gen_trans hu' (𝟙 Y') y (l₁ p hp) (gJ'.mem _ _), gen_trans hu (𝟙 Y') y (l₂ p hp) (gJ.mem _ _),
      mul_inv, mul_inv, mul_mul_mul_comm, mul_mul_mul_comm (trF _ _ (𝟙 Y') _ _ _)]
    refine congrArg₂ (· * ·) ?_ (hinv i y J J' gJ gJ')
    have e : ∀ {W : Scheme.{0}} (χ : Y ⟶ W), t i ≫ m ≫ χ = 𝟙 Y' ≫ m ≫ χ := fun χ => by
      rw [reassoc_of% ht i, Category.id_comp]
    exact congrArg₂ (fun a b => a * b⁻¹) (Finset.prod_congr rfl fun k _ => congrArg
      (fun ψ : Y' ⟶ X' => gm ψ y (L'.U (p.1 k) ⊓ L'.U (J' ψ)) (L'.g (p.1 k) (J' ψ)) ^ ε' k) (e (φ' k)))
      (Finset.prod_congr rfl fun k _ => congrArg
        (fun ψ : Y' ⟶ X => gm ψ y (L.U (p.2 k) ⊓ L.U (J ψ)) (L.g (p.2 k) (J ψ)) ^ ε k) (e (φ k)))

theorem lbIso_of_gens (hL : L.IsLB) (hL' : L'.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X'))
    (ε' : K' → ℤ) (u : LB.Gen (LB.LinComb L φ ε)) (hu : u.IsGen) (u' : LB.Gen (LB.LinComb L' φ' ε'))
    (hu' : u'.IsGen) : LBIso (LB.LinComb L φ ε) (LB.LinComb L' φ' ε') :=
  lbIso_of_invariant hL hL' φ ε φ' ε' (𝟙 Y) (I := PEmpty) PEmpty.elim (fun i => i.elim)
    (fun _ f _ => ⟨f, rfl, fun _ h => h⟩) _ (DVR.pullGen_isGen _ _ _ u hu (𝟙 Y)) _
    (DVR.pullGen_isGen _ _ _ u' hu' (𝟙 Y)) (fun i => i.elim)

def chartPullDiv (M N : LB Y) (f : Y' ⟶ Y) :
    ChartPull ((LB.div M N).pull f) (LB.div (M.pull f) (N.pull f)) (𝟙 Y') :=
  have le : ∀ J : PUnit → M.ι × N.ι, ((LB.div M N).pull f).U J ≤
      (M.pull f).U (fun _ => (J PUnit.unit).1) ⊓ (N.pull f).U (fun _ => (J PUnit.unit).2) := fun J y hy =>
    ⟨mem_pull.2 ((mem_pull (L := LB.div M N)).1 hy).1, mem_pull.2 ((mem_pull (L := LB.div M N)).1 hy).2⟩
  { idx := fun J => (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
    le := le
    g := fun y J J' hJ hJ' => by
      refine (gm_pull_g (LB.div M N) f (𝟙 Y') y J J' hJ hJ').trans ((gm_div N M (𝟙 Y' ≫ f) y _ _
        ⟨(mem_pull (L := LB.div M N)).1 hJ, (mem_pull (L := LB.div M N)).1 hJ'⟩).trans (Eq.symm ((gm_div (N.pull f) (M.pull f) (𝟙 Y') y
          (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
          (fun _ => (J' PUnit.unit).1, fun _ => (J' PUnit.unit).2) ⟨le J hJ, le J' hJ'⟩).trans ?_)))
      exact congrArg₂ (fun a b => a * b⁻¹) (gm_pull_g M f (𝟙 Y') y _ _ (le J hJ).1 (le J' hJ').1)
        (gm_pull_g N f (𝟙 Y') y _ _ (le J hJ).2 (le J' hJ').2) }

def chartPullFlat (L : LB X) (F : X' ⟶ X) (e : ℤ) (ψ : K → (Y ⟶ X')) (ε : K → ℤ) (f : Y' ⟶ Y) :
    ChartPull ((LB.LinComb (LB.LinComb L (K := PUnit) (fun _ => F) (fun _ => e)) ψ ε).pull f)
      (LB.LinComb L (fun k => f ≫ ψ k ≫ F) (fun k => ε k * e)) (𝟙 Y') :=
  have mem : ∀ (J : PUnit → K → PUnit → L.ι) (y : Y'),
      y ∈ ((LB.LinComb (LB.LinComb L (K := PUnit) (fun _ => F) (fun _ => e)) ψ ε).pull f).U J →
      ∀ k, ψ k (f y) ∈ LB.wchart L (fun _ : PUnit => F) (J PUnit.unit k) := fun J y hy k =>
    Set.mem_iInter.1 ((mem_pull (L := LB.LinComb (LB.LinComb L (K := PUnit) (fun _ => F) (fun _ => e)) ψ ε)).1 hy) k
  have le : ∀ J : PUnit → K → PUnit → L.ι,
      ((LB.LinComb (LB.LinComb L (K := PUnit) (fun _ => F) (fun _ => e)) ψ ε).pull f).U J ≤
        LB.wchart L (fun k => f ≫ ψ k ≫ F) (fun k => J PUnit.unit k PUnit.unit) := fun J y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 (mem J y hy k) PUnit.unit
  { idx := fun J k => J PUnit.unit k PUnit.unit
    le := le
    g := fun y J J' hJ hJ' => by
      refine (gm_pull_g _ f (𝟙 Y') y J J' hJ hJ').trans ((gm_linComb
        (LB.LinComb L (K := PUnit) (fun _ => F) (fun _ => e)) ψ ε (𝟙 Y' ≫ f) y (J PUnit.unit) (J' PUnit.unit)
        (Set.mem_iInter.2 (mem J y hJ)) (Set.mem_iInter.2 (mem J' y hJ'))).trans (Eq.trans
          (Finset.prod_congr rfl fun k _ => ?_) (gm_linComb L _ _ (𝟙 Y') y _ _ (le J hJ) (le J' hJ')).symm))
      refine (congrArg (· ^ ε k) (gm_linComb L (fun _ : PUnit => F) (fun _ => e) ((𝟙 Y' ≫ f) ≫ ψ k) y _ _
        (mem J y hJ k) (mem J' y hJ' k))).trans ?_
      rw [Fintype.prod_unique, ← zpow_mul, mul_comm e]
      simp only [Category.assoc] }

theorem exists_gen_div_pull {W : Scheme.{0}} (L : LB X) (L' : LB X') (F : W ⟶ X) (F' : W ⟶ X') (e e' : ℤ)
    (ψ : K → (Y ⟶ W)) (ε : K → ℤ) (f : Y' ⟶ Y)
    (H : LBIso (LB.LinComb L (fun k => f ≫ ψ k ≫ F) (fun k => ε k * e))
      (LB.LinComb L' (fun k => f ≫ ψ k ≫ F') (fun k => ε k * e'))) :
    ∃ t : LB.Gen ((LB.div (LB.LinComb (LB.LinComb L' (K := PUnit) (fun _ => F') (fun _ => e')) ψ ε)
      (LB.LinComb (LB.LinComb L (K := PUnit) (fun _ => F) (fun _ => e)) ψ ε)).pull f), t.IsGen := by
  obtain ⟨w, hw⟩ := H.chartPull (chartPullFlat L F e ψ ε f) (chartPullFlat L' F' e' ψ ε f)
  exact gen_chartPull (chartPullDiv _ _ f) w hw

end GlobalTheory.IsoDescent
