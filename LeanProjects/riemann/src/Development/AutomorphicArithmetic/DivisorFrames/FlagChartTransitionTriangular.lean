import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AutomorphicArithmetic.DivisorFrames.ExistsAdaptedFlagCharts
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

section SlopeTestRemainingChoices

open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (appLinear appLinear_apply)

private theorem UpperTheory.isFrame_of_map_eq_frame_injective {X : Scheme.{0}} {A M : X.Modules} {k r : ℕ} (hA : IsVB A k) (u : A ⟶ M)
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

private theorem UpperTheory.exists_flag_inclusion_of_le {X : Scheme.{0}} {M : X.Modules} {r : ℕ} (fl : Vert.Flag M r) (a b : Fin (r + 1))
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

private theorem UpperTheory.flag_section_combination {X : Scheme.{0}} {M : X.Modules} {r : ℕ} (fl : Vert.Flag M r) (ch : Chart M r)
    (hch : IsAdapted fl ch) (i : Fin r) (t : Γ(fl.F i.succ, ch.U)) (ht : (fl.ι i.succ).app ch.U t = ch.e i)
    {W : X.Opens} (hW : W ≤ ch.U) (y : Γ(fl.F i.succ, W)) :
    (∀ a, i < a → (ch.isFrame.basis hW).repr ((fl.ι i.succ).app W y) a = 0) ∧
      (fl.π i).app W y = (ch.isFrame.basis hW).repr ((fl.ι i.succ).app W y) i •
        resM (fl.gr i) hW ((fl.π i).app ch.U t) := by
  have hi : (i.succ : ℕ) ≤ r := i.2
  have key (j : Fin (i.succ : ℕ)) : ∃ s : Γ(fl.F i.succ, ch.U), (fl.ι i.succ).app ch.U s = ch.e (j.castLE hi) ∧
      (j = Fin.last i → s = t) ∧ (j ≠ Fin.last i → (fl.π i).app ch.U s = 0) := by
    by_cases hj : j = Fin.last i
    · subst hj
      exact ⟨t, ht, fun _ => rfl, fun h => (h rfl).elim⟩
    · obtain ⟨s₀, hs₀⟩ := hch (j.castLE hi)
      obtain ⟨φ, hφ⟩ := UpperTheory.exists_flag_inclusion_of_le fl (j.castLE hi).succ i.castSucc (Fin.val_lt_last hj)
      refine ⟨(φ ≫ fl.step i).app ch.U s₀, ?_, fun h => (hj h).elim, fun _ => ?_⟩
      · rw [QCoh.app_app, Category.assoc, fl.step_ι, hφ, hs₀]
      · have h₀ : fl.step i ≫ fl.π i = 0 := Limits.cokernel.condition _
        rw [QCoh.app_app, Category.assoc, h₀, Limits.comp_zero]
        rfl
  obtain ⟨l, hl₀⟩ : ∃ l : Fin (i.succ : ℕ), l = Fin.last i := ⟨_, rfl⟩
  have hlv : (l : ℕ) = i := congrArg Fin.val hl₀
  choose s hs h₁ h₂ using key
  have hf := UpperTheory.isFrame_of_map_eq_frame_injective (fl.isVB i.succ) (fl.ι i.succ) ch.isFrame _ (Fin.castLE_injective hi) s hs
  obtain ⟨c, rfl⟩ := (hf W hW).2 y
  have hι (a : Fin r) : (ch.isFrame.basis hW).repr ((fl.ι i.succ).app W
      (Fintype.linearCombination Γ(X, W) (fun j => resM (fl.F i.succ) hW (s j)) c)) a =
      ∑ j, if j.castLE hi = a then c j else 0 := by
    rw [Fintype.linearCombination_apply, ← appLinear_apply, map_sum, map_sum, Finsupp.coe_finset_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, appLinear_apply, app_resM, hs, ← ch.isFrame.basis_apply, map_smul, Module.Basis.repr_self,
      Finsupp.smul_apply, Finsupp.single_apply]
    split_ifs <;> simp
  refine ⟨fun a ha => ?_, ?_⟩
  · refine (hι a).trans (Finset.sum_eq_zero fun j _ => if_neg fun h => ?_)
    have h1 : (j : ℕ) = a := congrArg Fin.val h
    have h2 : (j : ℕ) < i + 1 := j.2
    have h3 : (i : ℕ) < a := ha
    omega
  · have hl : (∑ j : Fin (i.succ : ℕ), if j.castLE hi = i then c j else 0) = c l := by
      rw [Finset.sum_eq_single l, if_pos (Fin.ext hlv)]
      · intro j _ hj
        exact if_neg fun h => hj (Fin.ext ((show (j : ℕ) = i from congrArg Fin.val h).trans hlv.symm))
      · simp
    refine Eq.trans ?_ (congrArg (· • resM (fl.gr i) hW ((fl.π i).app ch.U t)) ((hι i).trans hl).symm)
    rw [Fintype.linearCombination_apply, ← appLinear_apply, map_sum,
      Finset.sum_eq_single l, map_smul, appLinear_apply, app_resM, h₁ _ hl₀]
    · intro j _ hj
      rw [map_smul, appLinear_apply, app_resM, h₂ j (fun h => hj (h.trans hl₀.symm)), map_zero, smul_zero]
    · simp

theorem UpperTheory.flag_chart_transition_triangular :
    ∀ (X : Scheme.{0}) (M : X.Modules) (r : ℕ) (fl : Vert.Flag M r) (ch ch' : Chart M r), IsAdapted fl ch → IsAdapted fl ch' → IsTri (trS ch ch') ∧ ∀ (i : Fin r) (t : Γ(fl.F i.succ, ch.U)) (t' : Γ(fl.F i.succ, ch'.U)), (fl.ι i.succ).app ch.U t = ch.e i → (fl.ι i.succ).app ch'.U t' = ch'.e i → ∀ (ht : IsFrame fun _ : Fin 1 => (fl.π i).app ch.U t) (ht' : IsFrame fun _ : Fin 1 => (fl.π i).app ch'.U t'), trS (⟨ch.U, _, ht⟩ : Chart (fl.gr i) 1) (⟨ch'.U, _, ht'⟩ : Chart (fl.gr i) 1) 0 0 = trS ch ch' i i := by
  intro X M r fl ch ch' h h'
  refine ⟨fun a i hia => ?_, fun i t t' e e' ht ht' => ?_⟩
  · obtain ⟨t, e⟩ := h i
    obtain ⟨t', e'⟩ := h' i
    have := (UpperTheory.flag_section_combination fl ch h i t e (W := ch.U ⊓ ch'.U) inf_le_left (resM _ inf_le_right t')).1 a hia
    rwa [app_resM, e'] at this
  · have := (UpperTheory.flag_section_combination fl ch h i t e (W := ch.U ⊓ ch'.U) inf_le_left (resM _ inf_le_right t')).2
    rw [app_resM, app_resM, e'] at this
    change (ht.basis inf_le_left).repr (resM (fl.gr i) inf_le_right ((fl.π i).app ch'.U t')) 0 =
      (ch.isFrame.basis inf_le_left).repr (resM M inf_le_right (ch'.e i)) i
    rw [this, ← ht.basis_apply inf_le_left 0, map_smul, Module.Basis.repr_self]
    simp

end SlopeTestRemainingChoices
