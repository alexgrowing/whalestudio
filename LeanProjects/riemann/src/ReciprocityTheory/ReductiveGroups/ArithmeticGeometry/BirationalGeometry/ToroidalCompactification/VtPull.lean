import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

section Germ

variable {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem mem_wchart_pull {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X)} {h : Y' ⟶ Y} (e : ∀ k, φ' k = h ≫ φ k)
    {j : K → L.ι} {y : Y'} (hy : y ∈ LB.wchart L φ' j) : h y ∈ LB.wchart L φ j := by
  unfold LB.wchart at hy ⊢
  simp only [TopologicalSpace.Opens.mem_mk, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe] at hy ⊢
  intro k
  first
    | simpa [e k] using hy k
    | (have hk := hy k; rw [e k] at hk; exact hk)

theorem exists_gen_pull (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (h : Y' ⟶ Y)
    (φ' : K → (Y' ⟶ X)) (e : ∀ k, φ' k = h ≫ φ k) :
    ∃ t' : LB.Gen (LB.LinComb L φ' ε), (t.IsGen → t'.IsGen) ∧ ∀ {Z : Scheme.{0}} (r : Z ⟶ Y') (z : Z) (j : K → L.ι),
      r z ∈ LB.wchart L φ' j → gm r z (LB.wchart L φ' j) (t'.s j) = gm (r ≫ h) z (LB.wchart L φ j) (t.s j) := by
  obtain rfl : φ' = fun k => h ≫ φ k := funext e
  refine ⟨LB.pullGen L φ ε t h, fun ht => pullGen_isGen L φ ε t ht h, fun r z j hz => ?_⟩
  exact (gm_res r z _ hz _).trans (gm_pull r h z (LB.wchart L φ j) (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz k) _)

theorem exists_sec_pull (φ : K → (Y ⟶ X)) (ε : K → ℤ) (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y)
    (φ' : K → (Y' ⟶ X)) (e : ∀ k, φ' k = h ≫ φ k) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), ∀ {Z : Scheme.{0}} (r : Z ⟶ Y') (z : Z) (j : K → L.ι),
      r z ∈ LB.wchart L φ' j → gs r z (LB.wchart L φ' j) (s'.f j) = gs (r ≫ h) z (LB.wchart L φ j) (s.f j) := by
  obtain rfl : φ' = fun k => h ≫ φ k := funext e
  refine ⟨pullSec L φ ε s h, fun r z j hz => ?_⟩
  exact (gs_res r z _ hz _).trans (gs_pull r h z (LB.wchart L φ j) (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz k) _)

theorem val_of_pull {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K → (Y' ⟶ X)} {h : Y' ⟶ Y} (e : ∀ k, φ' k = h ≫ φ k)
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε)}
    (H : ∀ {Z : Scheme.{0}} (r : Z ⟶ Y') (z : Z) (j : K → L.ι),
      r z ∈ LB.wchart L φ' j → gm r z (LB.wchart L φ' j) (t'.s j) = gm (r ≫ h) z (LB.wchart L φ j) (t.s j))
    {Z : Scheme.{0}} (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val t' r z J = val t (r ≫ h) z J := by
  obtain rfl : φ' = fun k => h ≫ φ k := funext e
  unfold val
  simp only [Category.assoc]
  rw [H]
  all_goals first
    | rfl
    | (unfold LB.wchart
       simp only [TopologicalSpace.Opens.mem_mk, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
       intro k
       simpa using hJ (r ≫ h ≫ φ k))
    | (simp only [LB.wchart, TopologicalSpace.Opens.mem_mk, Set.mem_iInter, Set.mem_preimage]
       intro k
       simpa using hJ (r ≫ h ≫ φ k))
    | (simp [Category.assoc])
    | (congr 1)

end Germ

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

section Nat

variable {T T' : Over S} (σ : T' ⟶ T)

theorem whisk_fst : (σ ▷ A) ≫ fst T A = fst T' A ≫ σ := by
  first
    | exact whiskerRight_fst σ A
    | (simp; done)
    | exact CartesianMonoidalCategory.whiskerRight_fst σ A

theorem whisk_snd : (σ ▷ A) ≫ snd T A = snd T' A := by
  first
    | exact whiskerRight_snd σ A
    | (simp; done)

theorem translPt_whisk (x : T ⟶ A) : (σ ▷ A) ≫ translPt A x = translPt A (σ ≫ x) := by
  first
    | (simp only [translPt, comp_lift_assoc, whiskerRight_fst_assoc, whiskerRight_snd]; done)
    | (simp [translPt]; done)
    | (unfold translPt; rw [comp_lift_assoc, whiskerRight_fst_assoc, whiskerRight_snd])

theorem transl_whisk (x : T ⟶ A) : translT A (σ ≫ x) ≫ (σ ▷ A) = (σ ▷ A) ≫ translT A x := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · simp [translT, translPt_whisk]

theorem neg_whisk : negT A T' ≫ (σ ▷ A) = (σ ▷ A) ≫ negT A T := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [negT]
  · simp [negT]

theorem mul_whisk (N : ℕ) : mulT A T' N ≫ (σ ▷ A) = (σ ▷ A) ≫ mulT A T N := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [mulT]
  · first
      | (simp [mulT, comp_pow]; done)
      | (simp [mulT]; done)
      | (simp only [mulT, Category.assoc, whiskerRight_snd, lift_snd]
         induction N with
         | zero => simp
         | succ n ih => simp [pow_succ, comp_mul, ih])

end Nat

def PullRel (L : LB A.left) (a : ℤ) {T T' : Over S} (h : T' ⊗ A ⟶ T ⊗ A) (s : LB.Sec (LPow A L a T))
    (s' : LB.Sec (LPow A L a T')) : Prop :=
  ∀ {Z : Scheme.{0}} (r : Z ⟶ (T' ⊗ A).left) (z : Z) (j : Fin 1 → L.ι), r z ∈ (LPow A L a T').U j →
    gs r z ((LPow A L a T').U j) (s'.f j) = gs (r ≫ h.left) z ((LPow A L a T).U j) (s.f j)

theorem pullRel_of {L : LB A.left} {a : ℤ} {T T' : Over S} {h : T' ⊗ A ⟶ T ⊗ A} {hh : h ≫ snd T A = snd T' A}
    {s : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T')} (H : IsPullSec A L a h hh s s') : PullRel L a h s s' := by
  intro Z r z j hz
  rw [H j]
  have hz1 : r z ∈ h.left ⁻¹ᵁ (LPow A L a T).U j := chart_le_res A L h hh a j hz
  have hz2 : (r ≫ h.left) z ∈ (LPow A L a T).U j := by
    first
      | exact hz1
      | simpa using hz1
  unfold gs
  rw [dif_pos hz, dif_pos hz2]
  have k1 := congrArg (fun g => g.hom (((T' ⊗ A).left.presheaf.map
    (homOfLE (chart_le_res A L h hh a j)).op).hom ((h.left.app _).hom (s.f j))))
    (Scheme.Hom.germ_stalkMap r _ z hz)
  have k2 := congrArg (fun g => g.hom ((h.left.app _).hom (s.f j))) (Scheme.Hom.germ_stalkMap r _ z hz1)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at k1 k2
  rw [← k1]
  erw [TopCat.Presheaf.germ_res_apply]
  exact k2

theorem exists_pullRel (L : LB A.left) (a : ℤ) {T T' : Over S} (h : T' ⊗ A ⟶ T ⊗ A) (hh : h ≫ snd T A = snd T' A)
    (s : LB.Sec (LPow A L a T)) : ∃ s' : LB.Sec (LPow A L a T'), PullRel L a h s s' :=
  exists_sec_pull _ _ s h.left _ fun _ => by rw [← Over.comp_left, hh]

theorem twist_pull {L : LB A.left} {T T' : Over S} (h : T' ⊗ A ⟶ T ⊗ A) (hh : h ≫ snd T A = snd T' A)
    {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {ψ' : T' ⊗ A ⟶ T' ⊗ A} {m' : T' ⊗ A ⟶ A}
    {hm' : ψ' ≫ snd T' A = m'} (hψ : ψ' ≫ h = h ≫ ψ) {a b : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])}
    {α' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T' A).left, m'.left] ![a, -b])}
    (hα : ∀ {Z : Scheme.{0}} (r : Z ⟶ (T' ⊗ A).left) (z : Z) (j : Fin 2 → L.ι),
      r z ∈ LB.wchart L ![(snd T' A).left, m'.left] j →
        gm r z (LB.wchart L ![(snd T' A).left, m'.left] j) (α'.s j) =
          gm (r ≫ h.left) z (LB.wchart L ![(snd T A).left, m.left] j) (α.s j))
    {s : LB.Sec (LPow A L b T)} {s₁ : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L b T')}
    {s₁' : LB.Sec (LPow A L a T')} (hs : PullRel L b h s s') (hs₁ : PullRel L a h s₁ s₁')
    (tw : IsTwistPull A L ψ m hm a b α s s₁) : IsTwistPull A L ψ' m' hm' a b α' s' s₁' := by
  have e1 : h.left ≫ (snd T A).left = (snd T' A).left := by rw [← Over.comp_left, hh]
  have e2 : h.left ≫ m.left = m'.left := by
    rw [← Over.comp_left, ← hm, ← hm', ← Category.assoc, ← hψ, Category.assoc, hh]
  have e : ∀ k, (![(snd T' A).left, m'.left] : Fin 2 → _) k = h.left ≫ (![(snd T A).left, m.left] : Fin 2 → _) k := by
    intro k; fin_cases k
    · exact e1.symm
    · exact e2.symm
  have eψ : ψ'.left ≫ h.left = h.left ≫ ψ.left := by rw [← Over.comp_left, hψ, Over.comp_left]
  intro j
  refine fn_ext fun y hy => ?_
  have hy' := mem_wchart_pull e hy
  have t1 := congrArg (gs h.left y (LB.wchart L ![(snd T A).left, m.left] j)) (tw j)
  erw [gs_res _ y _ hy', gs_mul _ y _ hy', gs_unit _ y _ hy', gs_res _ y _ hy',
    gs_pull h.left ψ.left y (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1))
      (chart_le_pull A L ψ m hm j hy')] at t1
  erw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_unit _ y _ hy, gs_res _ y _ hy,
    gs_pull (𝟙 _) ψ'.left y (LB.wchart L (fun _ : Fin 1 => (snd T' A).left) (fun _ => j 1))
      (chart_le_pull A L ψ' m' hm' j hy), hs₁ _ y _ (chart_le_zero A L m' j hy), hα _ y j hy,
    hs _ y _ (chart_le_pull A L ψ' m' hm' j hy)]
  erw [eψ]
  exact t1

section Theta

variable {L : LB A.left} {k : ℤ}

theorem val_powGenT {T : Over S} (θ : ThetaGrp A L k T) (n : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    {J : (Z ⟶ A.left) → L.ι} (hJ : Good L z J) :
    val (powGen A L k θ n) r z J = ∏ j₀ : Fin n, val θ.φ (r ≫ (translT A (θ.pt ^ (j₀ : ℕ))).left) z J := by
  have e : ∀ j₀ : Fin n, val (LB.pullGen L _ _ θ.φ (translT A (θ.pt ^ (j₀ : ℕ))).left) r z J =
      val θ.φ (r ≫ (translT A (θ.pt ^ (j₀ : ℕ))).left) z J := fun j₀ => val_pull hJ _ _ _
  simp only [← e]
  simp only [val, powGen]
  exact (map_prod _ _ _).trans (Finset.prod_congr rfl fun j₀ _ => gm_res r z _ (hJ.mem (powφ A θ.pt n) r) _)

theorem val_symGen {T : Over S} (θ : ThetaGrp A L k T) (nu : LB.Gen (negLB A L k T)) {Z : Scheme.{0}}
    (r : Z ⟶ (T ⊗ A).left) (z : Z) {J : (Z ⟶ A.left) → L.ι} (hJ : Good L z J) :
    val (symGen A L k θ nu) r z J = val θ.φ (r ≫ (translT A θ.pt⁻¹).left) z J * val nu r z J *
      (val θ.φ (r ≫ (negT A T).left) z J * (val nu (r ≫ (translT A θ.pt⁻¹).left) z J)⁻¹) := by
  unfold symGen
  exact (val_mul hJ _ _ r).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ r).trans (congrArg₂ (· * ·) (val_pull hJ _ _ r) rfl))
    ((val_mul hJ _ _ r).trans (congrArg₂ (· * ·) (val_pull hJ _ _ r) ((val_inv _ r).trans (congrArg (·⁻¹) (val_pull hJ _ _ r))))))

theorem eθ {T T' : Over S} (σ : T' ⟶ T) (x : T ⟶ A) :
    ∀ kk, (![(snd T' A).left, (translPt A (σ ≫ x)).left] : Fin 2 → _) kk =
      (σ ▷ A).left ≫ (![(snd T A).left, (translPt A x).left] : Fin 2 → _) kk := by
  intro kk
  fin_cases kk
  · simp [← Over.comp_left]
  · simp [← Over.comp_left, translPt_whisk]

theorem exists_phi_pull {T T' : Over S} (σ : T' ⟶ T) (θ : ThetaGrp A L k T) :
    ∃ φ' : LB.Gen (thetaLB A L k (σ ≫ θ.pt)), φ'.IsGen ∧ ∀ {Z : Scheme.{0}} (r : Z ⟶ (T' ⊗ A).left) (z : Z)
      (j : Fin 2 → L.ι), r z ∈ LB.wchart L ![(snd T' A).left, (translPt A (σ ≫ θ.pt)).left] j →
        gm r z (LB.wchart L ![(snd T' A).left, (translPt A (σ ≫ θ.pt)).left] j) (φ'.s j) =
          gm (r ≫ (σ ▷ A).left) z (LB.wchart L ![(snd T A).left, (translPt A θ.pt).left] j) (θ.φ.s j) := by
  obtain ⟨φ', g, H⟩ := exists_gen_pull (L := L) ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] θ.φ (σ ▷ A).left
    ![(snd T' A).left, (translPt A (σ ≫ θ.pt)).left] (eθ σ θ.pt)
  exact ⟨φ', g θ.isGen, H⟩

theorem symLift_pull (hL : L.IsLB) {T T' : Over S} (σ : T' ⟶ T) {n : ℕ} {x : T ⟶ A} {θ : ThetaGrp A L k T}
    (hθ : SymLift A L k n x θ) (φ' : LB.Gen (thetaLB A L k (σ ≫ θ.pt))) (gφ' : φ'.IsGen)
    (hv : ∀ {Z : Scheme.{0}} (r : Z ⟶ (T' ⊗ A).left) (z : Z) {J : (Z ⟶ A.left) → L.ι}, Good L z J →
      val φ' r z J = val θ.φ (r ≫ (σ ▷ A).left) z J) :
    SymLift A L k n (σ ≫ x) ⟨σ ≫ θ.pt, φ', gφ'⟩ where
  pt_eq := by
    show σ ≫ θ.pt = σ ≫ x
    rw [hθ.pt_eq]
  pow_eq := by
    refine corr_of_val hL fun y J hJ => ?_
    have c := val_corr hJ hθ.pow_eq (σ ▷ A).left
    rw [val_powGenT θ n _ y hJ, val_one] at c
    rw [val_powGenT _ n _ y hJ, val_one, ← c]
    refine Finset.prod_congr rfl fun j₀ _ => ?_
    have m : (𝟙 _ ≫ (translT A ((σ ≫ θ.pt) ^ (j₀ : ℕ))).left) ≫ (σ ▷ A).left =
        (σ ▷ A).left ≫ (translT A (θ.pt ^ (j₀ : ℕ))).left := by
      rw [Category.id_comp, ← MonObj.comp_pow, ← Over.comp_left, ← Over.comp_left, transl_whisk]
    exact (hv _ y hJ).trans (by rw [m])
  sym := by
    obtain ⟨nu, gnu, cnu⟩ := hθ.sym
    have e1 : (σ ▷ A).left ≫ (snd T A).left = (snd T' A).left := by rw [← Over.comp_left, whisk_snd]
    have e2 : (σ ▷ A).left ≫ (snd T A ≫ (GrpObj.inv : A ⟶ A)).left = (snd T' A ≫ (GrpObj.inv : A ⟶ A)).left := by
      rw [← Over.comp_left, ← Category.assoc, whisk_snd]
    have eN : ∀ kk, (![(snd T' A).left, (snd T' A ≫ (GrpObj.inv : A ⟶ A)).left] : Fin 2 → _) kk =
        (σ ▷ A).left ≫ (![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left] : Fin 2 → _) kk := by
      intro kk; fin_cases kk
      · exact e1.symm
      · exact e2.symm
    obtain ⟨nu', gnu', Hnu⟩ := exists_gen_pull (L := L) _ ![k, -k] nu (σ ▷ A).left _ eN
    refine ⟨nu', gnu' gnu, corr_of_val hL fun y J hJ => ?_⟩
    have c := val_corr hJ cnu (σ ▷ A).left
    rw [val_symGen θ nu _ y hJ, val_one] at c
    rw [val_symGen _ nu' _ y hJ, val_one, ← c]
    have m1 : (𝟙 _ ≫ (translT A (σ ≫ θ.pt)⁻¹).left) ≫ (σ ▷ A).left = (σ ▷ A).left ≫ (translT A θ.pt⁻¹).left := by
      rw [Category.id_comp, ← GrpObj.comp_inv, ← Over.comp_left, ← Over.comp_left, transl_whisk]
    have m3 : (𝟙 _ ≫ (negT A T').left) ≫ (σ ▷ A).left = (σ ▷ A).left ≫ (negT A T).left := by
      rw [Category.id_comp, ← Over.comp_left, ← Over.comp_left, neg_whisk]
    have v1 := hv (𝟙 _ ≫ (translT A (σ ≫ θ.pt)⁻¹).left) y hJ
    have v2 := hv (𝟙 _ ≫ (negT A T').left) y hJ
    have v3 := val_of_pull eN Hnu (𝟙 _) y hJ
    have v4 := val_of_pull eN Hnu (𝟙 _ ≫ (translT A (σ ≫ θ.pt)⁻¹).left) y hJ
    rw [m1] at v1 v4
    rw [m3] at v2
    rw [Category.id_comp] at v3
    exact congrArg₂ (· * ·) (congrArg₂ (· * ·) v1 v3) (congrArg₂ (· * ·) v2 (congrArg (·⁻¹) v4))

end Theta

variable [IsCommMonObj A]

theorem vtOver_pull (L : RigLB A) (N : ℕ) {T T' : Over S} (σ : T' ⟶ T) {ok : (T ⟶ A) → Prop}
    {ok' : (T' ⟶ A) → Prop} (hok : ∀ x, ok x → ok' (σ ≫ x)) {s : LB.Sec (LPow A L.L 1 T)}
    {s' : LB.Sec (LPow A L.L 1 T')} {t : T ⟶ A} {F : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)}
    {F' : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T')}
    (hs : IsPullSec A L.L 1 (σ ▷ A) (whiskerRight_snd σ A) s s')
    (hF : IsPullSec A L.L ((N : ℤ) ^ 2) (σ ▷ A) (whiskerRight_snd σ A) F F') (h : VtOver L N ok s t F) :
    VtOver L N ok' s' (σ ≫ t) F' := by
  obtain ⟨t', α₀, α, s₁, U, ht, o, g₀, n₀, cα, tw, sl, ac⟩ := h
  have e1 : (σ ▷ A).left ≫ (snd T A).left = (snd T' A).left := by rw [← Over.comp_left, whisk_snd]
  have e2 : (σ ▷ A).left ≫ (snd T A ^ N).left = (snd T' A ^ N).left := by
    rw [← Over.comp_left, MonObj.comp_pow, whisk_snd]
  have eα : ∀ kk, (![(snd T' A).left, (snd T' A ^ N).left] : Fin 2 → _) kk =
      (σ ▷ A).left ≫ (![(snd T A).left, (snd T A ^ N).left] : Fin 2 → _) kk := by
    intro kk; fin_cases kk
    · exact e1.symm
    · exact e2.symm
  obtain ⟨α', -, hα'⟩ := exists_gen_pull (L := L.L) _ _ α (σ ▷ A).left _ eα
  obtain ⟨s₁', hs₁'⟩ := exists_pullRel L.L ((N : ℤ) ^ 2) (σ ▷ A) (whiskerRight_snd σ A) s₁
  obtain ⟨φ', gφ', HU⟩ := exists_phi_pull σ U
  refine ⟨σ ≫ t', α₀, α', s₁', ⟨σ ≫ U.pt, φ', gφ'⟩, by rw [← MonObj.comp_pow, ht], hok _ o, g₀, n₀, ?_, ?_, ?_, ?_⟩
  · refine corr_of_val L.isLB fun y J hJ => ?_
    rw [val_of_pull eα hα' _ y hJ, val_corr hJ cα, val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp, e1]
  · exact twist_pull (σ ▷ A) (whiskerRight_snd σ A) (mul_whisk σ N) hα' (pullRel_of hs) hs₁' tw
  · exact symLift_pull L.isLB σ sl φ' gφ' fun r z J hJ => val_of_pull (eθ σ U.pt) HU r z hJ
  · exact twist_pull (σ ▷ A) (whiskerRight_snd σ A) (transl_whisk σ U.pt) HU hs₁' (pullRel_of hF) ac

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
