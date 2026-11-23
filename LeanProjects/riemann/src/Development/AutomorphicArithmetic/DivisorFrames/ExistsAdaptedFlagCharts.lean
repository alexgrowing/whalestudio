import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

section SlopeTestRemainingChoices

open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (appLinear appLinear_apply)

private theorem UpperTheory.subbundle_frame_of_injective {X : Scheme.{0}} {A M : X.Modules} {k r : ℕ} (hA : IsVB A k) (u : A ⟶ M)
    {U : X.Opens} {e : Fin r → Γ(M, U)} (he : IsFrame e) (g : Fin k → Fin r) (hg : Function.Injective g)
    (s : Fin k → Γ(A, U)) (hs : ∀ j, u.app U (s j) = e (g j)) : IsFrame s := by
  refine isFrame_of_forall_exists fun V h x hx => ?_
  obtain ⟨W, a, -, hxW, hle, ha⟩ := hA.exists_affine hx
  refine ⟨W, hle, hxW, ?_⟩
  let p : Γ(A, W) →ₗ[Γ(X, W)] (Fin k → Γ(X, W)) :=
    LinearMap.funLeft _ _ g ∘ₗ (he.basis (hle.trans h)).equivFun.toLinearMap ∘ₗ appLinear u W
  have hp : p ∘ₗ (Fintype.linearCombination Γ(X, W) fun i => resM A (hle.trans h) (s i)) = LinearMap.id := by
    refine (Pi.basisFun _ _).ext fun j => ?_
    have h₁ : appLinear u W (resM A (hle.trans h) (s j)) = he.basis (hle.trans h) (g j) := by
      rw [appLinear_apply, app_resM, hs, IsFrame.basis_apply]
    funext i
    simp [p, h₁, Finsupp.single_apply, Pi.single_apply, hg.eq_iff, eq_comm, -IsFrame.basis_apply]
  have hp' (c) : p (Fintype.linearCombination Γ(X, W) (fun i => resM A (hle.trans h) (s i)) c) = c :=
    LinearMap.congr_fun hp c
  have hsurj : Function.Surjective p := fun c => ⟨_, hp' c⟩
  have hinj : Function.Injective p := by
    have := OrzechProperty.injective_of_surjective_endomorphism
      (p ∘ₗ (ha.basis le_rfl).equivFun.symm.toLinearMap) (hsurj.comp (ha.basis le_rfl).equivFun.symm.surjective)
    exact (Function.Injective.of_comp_iff' _ (ha.basis le_rfl).equivFun.symm.bijective).1 this
  exact ⟨fun c c' hc => by rw [← hp' c, hc, hp'], fun y => ⟨p y, hinj (hp' _)⟩⟩

private theorem UpperTheory.quotient_line_frame {X : Scheme.{0}} {A L : X.Modules} {k : ℕ} (hL : IsVB L 1) (q : A ⟶ L) [Epi q]
    {U : X.Opens} {s : Fin k → Γ(A, U)} (hs : IsFrame s) (j₀ : Fin k) (h₀ : ∀ j, j ≠ j₀ → q.app U (s j) = 0) :
    IsFrame fun _ : Fin 1 => q.app U (s j₀) := by
  refine isFrame_of_forall_exists fun V h x hx => ?_
  obtain ⟨W', c, -, hxW', hle', hc⟩ := hL.exists_affine hx
  obtain ⟨W, hW, hxW, t, ht⟩ := VBExt.exists_lifts q c hxW'
  have hle := hW.trans hle'
  refine ⟨W, hle, hxW, ?_⟩
  obtain ⟨a, ha⟩ := (hs W (hle.trans h)).2 (t 0)
  have h₁ : resM L hW (c 0) = a j₀ • resM L (hle.trans h) (q.app U (s j₀)) := by
    rw [← ht, ← ha, Fintype.linearCombination_apply, ← appLinear_apply, map_sum, Finset.sum_eq_single j₀, map_smul,
      appLinear_apply, app_resM]
    · intro j _ hj
      rw [map_smul, appLinear_apply, app_resM, h₀ j hj, map_zero, smul_zero]
    · simp
  have hsurj : Function.Surjective
      (Fintype.linearCombination Γ(X, W) fun _ : Fin 1 => resM L (hle.trans h) (q.app U (s j₀))) := fun y => by
    obtain ⟨b, rfl⟩ := (hc W hW).2 y
    refine ⟨fun _ => b 0 * a j₀, ?_⟩
    simp only [Fintype.linearCombination_apply, Fin.sum_univ_one, h₁, smul_smul]
  refine ⟨?_, hsurj⟩
  have hg := OrzechProperty.injective_of_surjective_endomorphism ((hc.basis hW).equivFun.toLinearMap ∘ₗ
    (Fintype.linearCombination Γ(X, W) fun _ : Fin 1 => resM L (hle.trans h) (q.app U (s j₀))))
    ((hc.basis hW).equivFun.surjective.comp hsurj)
  exact Function.Injective.of_comp (f := ⇑(hc.basis hW).equivFun) hg

private theorem UpperTheory.flag_nested {X : Scheme.{0}} {M : X.Modules} {r : ℕ} (fl : Vert.Flag M r) (a b : Fin (r + 1))
    (h : a ≤ b) : ∃ φ : fl.F a ⟶ fl.F b, φ ≫ fl.ι b = fl.ι a := by
  induction b using Fin.induction with
  | zero =>
    obtain rfl : a = 0 := Fin.le_zero_iff.1 h
    exact ⟨𝟙 _, Category.id_comp _⟩
  | succ b ih =>
    rcases h.eq_or_lt with rfl | h'
    · exact ⟨𝟙 _, Category.id_comp _⟩
    · obtain ⟨φ, hφ⟩ := ih (Fin.le_castSucc_iff.2 h')
      exact ⟨φ ≫ fl.step b, by rw [Category.assoc, fl.step_ι, hφ]⟩

private theorem UpperTheory.flag_local_frames {X : Scheme.{0}} {M : X.Modules} {r : ℕ} (fl : Vert.Flag M r) (x : X)
    (k : Fin (r + 1)) : ∃ (U : X.Opens) (s : Fin k → Γ(fl.F k, U)), x ∈ U ∧ IsFrame s ∧
      ∀ (j : Fin k) (i : Fin r), (i : ℕ) = j →
        ∃ s₀ : Γ(fl.F i.succ, U), (fl.ι i.succ).app U s₀ = (fl.ι k).app U (s j) := by
  induction k using Fin.induction with
  | zero =>
    obtain ⟨U, s, hx, hs⟩ := fl.isVB 0 x
    exact ⟨U, s, hx, hs, fun j => j.elim0⟩
  | succ k ih =>
    obtain ⟨U, s, hx, hs, H⟩ := ih
    obtain ⟨U', c, -, hx', hle, hc⟩ := (fl.isVB_gr k).exists_affine hx
    obtain ⟨W, hW, hxW, t, ht⟩ := VBExt.exists_lifts (fl.π k) c hx'
    have ht' : IsFrame fun j => (fl.π k).app W (t j) := by rw [funext ht]; exact hc.res hW
    have hf := (VBExt.isFrame_sumElim (VMetric.stepSeq_shortExact fl k) (hs.res (hW.trans hle)) ht').comp_equiv
      finSumFinEquiv.symm
    refine ⟨W, _, hxW, hf, fun j i hij => ?_⟩
    obtain ⟨j, rfl⟩ := (finSumFinEquiv (m := k.castSucc) (n := 1)).surjective j
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rcases j with j | j
    · obtain ⟨s₀, hs₀⟩ := H j i hij
      refine ⟨resM _ (hW.trans hle) s₀, ?_⟩
      rw [app_resM, hs₀, ← app_resM, ← fl.step_ι]
      rfl
    · obtain rfl : i = k := Fin.ext (by rw [hij, Subsingleton.elim j 0]; rfl)
      exact ⟨_, rfl⟩

end SlopeTestRemainingChoices

theorem UpperTheory.exists_adapted_flag_charts :
    ∀ (X : Scheme.{0}) (M : X.Modules) (r : ℕ) (fl : Vert.Flag M r), (∀ x : X, ∃ ch : Chart M r, x ∈ ch.U ∧ IsAdapted fl ch) ∧ ∀ ch : Chart M r, IsAdapted fl ch → ∀ (i : Fin r) (t : Γ(fl.F i.succ, ch.U)), (fl.ι i.succ).app ch.U t = ch.e i → IsFrame fun _ : Fin 1 => (fl.π i).app ch.U t := by
  intro X M r fl
  refine ⟨fun x => ?_, fun ch hch i t ht => ?_⟩
  · obtain ⟨U, s, hx, hs, H⟩ := UpperTheory.flag_local_frames fl x (Fin.last r)
    exact ⟨⟨U, _, hs.map_iso (fl.ι (Fin.last r))⟩, hx, fun i => H i i rfl⟩
  · have hi : (i.succ : ℕ) ≤ r := i.2
    have key (j : Fin (i.succ : ℕ)) : ∃ s : Γ(fl.F i.succ, ch.U), (fl.ι i.succ).app ch.U s = ch.e (j.castLE hi) ∧
        (j = Fin.last i → s = t) ∧ (j ≠ Fin.last i → (fl.π i).app ch.U s = 0) := by
      by_cases hj : j = Fin.last i
      · subst hj
        exact ⟨t, ht, fun _ => rfl, fun h => (h rfl).elim⟩
      · obtain ⟨s₀, hs₀⟩ := hch (j.castLE hi)
        obtain ⟨φ, hφ⟩ := UpperTheory.flag_nested fl (j.castLE hi).succ i.castSucc (Fin.val_lt_last hj)
        refine ⟨(φ ≫ fl.step i).app ch.U s₀, ?_, fun h => (hj h).elim, fun _ => ?_⟩
        · rw [QCoh.app_app, Category.assoc, fl.step_ι, hφ, hs₀]
        · have h₀ : fl.step i ≫ fl.π i = 0 := Limits.cokernel.condition _
          rw [QCoh.app_app, Category.assoc, h₀, Limits.comp_zero]
          rfl
    choose s hs h₁ h₂ using key
    have := UpperTheory.quotient_line_frame (fl.isVB_gr i) (fl.π i)
      (UpperTheory.subbundle_frame_of_injective (fl.isVB i.succ) (fl.ι i.succ) ch.isFrame _ (Fin.castLE_injective hi) s hs) (Fin.last i) h₂
    rwa [h₁ _ rfl] at this
