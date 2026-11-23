import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodPlaceAvoidsBadSetsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodPlaceHeckeEigenMatchStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointsEqualEigenMatchStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EigSplit

open Formalism.IndefR.Links in
theorem cast_add {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) (x y : D.what₂.Mt μ a) :
    (h ▸ (x + y) : D.what₂.Mt μ b) = (h ▸ x : D.what₂.Mt μ b) + (h ▸ y : D.what₂.Mt μ b) := by
  subst h; rfl

theorem cast_zero {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) :
    (h ▸ (0 : D.what₂.Mt μ a) : D.what₂.Mt μ b) = 0 := by
  subst h; rfl

theorem cast_inj {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) {x y : D.what₂.Mt μ a}
    (hxy : (h ▸ x : D.what₂.Mt μ b) = (h ▸ y : D.what₂.Mt μ b)) : x = y := by
  subst h; exact hxy

theorem cast_symm {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) (m : D.what₂.Mt μ b) :
    (h ▸ (h.symm ▸ m : D.what₂.Mt μ a) : D.what₂.Mt μ b) = m := by
  subst h; rfl

theorem fn_zero {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    {μ : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) : X.fn hμ j 0 = 0 := by
  unfold GlobalTheory.NJoin.RealAt.fn; simp; rfl

theorem fn_add {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    {μ : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (x y : D.what₂.Mt μ (j.1 + 1)) :
    X.fn hμ j (x + y) = X.fn hμ j x + X.fn hμ j y := by
  unfold GlobalTheory.NJoin.RealAt.fn; simp; rfl

theorem rep_mem {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (Pp : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ)
    {γ : Formalism.L2.Theta.GA D V} (hγ : γ ∈ GlobalTheory.Hk3.rep V Pp d) : γ ∈ Formalism.L2.Theta.GfC V := by
  unfold GlobalTheory.Hk3.rep at hγ
  split_ifs at hγ with hl
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hR⟩ := hl.choose_spec
    exact (hR.1 γ hγ).1
  · simp at hγ

theorem twist_eq {G H W : Type*} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] (ρ : G →* Module.End ℂ W)
    (rr : G →* H) (F : H → W) (g γ : G) (h1 : ρ γ⁻¹ = 1) :
    ρ (g * γ)⁻¹ (F (rr (g * γ))) = ρ g⁻¹ (F (rr g * rr γ)) := by
  rw [mul_inv_rev, map_mul, map_mul, h1, one_mul]

theorem sum_single_one {W : Type*} [AddCommGroup W] [Module ℂ W] (d : List ℤ) (S : List ℤ → W) :
    (Finsupp.single d (1 : ℂ)).sum (fun d z => z • S d) = S d := by
  rw [Finsupp.sum_single_index (h := fun d (z : ℂ) => z • S d) (zero_smul ℂ _), one_smul]

theorem transport {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    (j : Fin D.R.m) (t : X.T) (h : DIV.Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (X.R.HV j t).H)
    (hh : GlobalTheory.Hk3.IsOpsV X.R j t h) (Pp : DIV.Pl D.host.E) (hG : GlobalTheory.Hk3.Good X.R t Pp) (d : List ℤ)
    (y : (X.R.HV j t).H) (c : ℂ)
    (hc : ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.R.extV j t y (g * γ) = c • X.R.extV j t y g) :
    h Pp (Finsupp.single d 1) y = c • y := by
  have hcv := (X.given.core.models.cV j).1
  apply X.hinj j t
  funext g
  have e1 : X.R.extV j t (c • y) g = c • X.R.extV j t y g :=
    congrFun ((X.R.extV j t).map_smul c y) g
  have e3 : ∀ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.R.extV j t y (g * γ) =
      (X.R.cV j).ρ g⁻¹ ((X.R.HV j t).e y ((Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict g *
        (Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict γ)) := by
    intro γ hγ
    exact twist_eq (X.R.cV j).ρ (Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict ((X.R.HV j t).e y) g γ
      (hcv γ⁻¹ (inv_mem (rep_mem _ Pp d hγ)))
  have e2 : X.R.extV j t (h Pp (Finsupp.single d 1) y) g =
      ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.R.extV j t y (g * γ) := by
    refine Eq.trans ?_ (Finset.sum_congr rfl e3).symm
    show (X.R.cV j).ρ g⁻¹ ((X.R.HV j t).e (h Pp (Finsupp.single d 1) y)
      ((Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict g)) = _
    refine Eq.trans (congrArg ((X.R.cV j).ρ g⁻¹) (congrFun (hh Pp hG (Finsupp.single d 1) y)
      ((Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict g))) ?_
    unfold GlobalTheory.Hk3.hkF
    exact (congrArg ((X.R.cV j).ρ g⁻¹) (sum_single_one d _)).trans (map_sum ((X.R.cV j).ρ g⁻¹) _ _)
  exact e2.trans ((hc g).trans e1.symm)

theorem eig_zero {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    {μ : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (Pp : DIV.Pl D.host.E) (d : List ℤ) (c : ℂ) :
    ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j 0 (g * γ) = c • X.fn hμ j 0 g := by
  intro g
  rw [fn_zero]
  simp

theorem eig_add {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    {μ : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (Pp : DIV.Pl D.host.E) (d : List ℤ) (c : ℂ)
    (f₁ f₂ : D.what₂.Mt μ (j.1 + 1)) (h₁ : ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f₁ (g * γ) = c • X.fn hμ j f₁ g) (h₂ : ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f₂ (g * γ) = c • X.fn hμ j f₂ g) :
    ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j (f₁ + f₂) (g * γ) = c • X.fn hμ j (f₁ + f₂) g := by
  intro g
  rw [fn_add]
  simp only [Pi.add_apply, Finset.sum_add_distrib, smul_add, h₁ g, h₂ g]

theorem alongEig {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (x : D.nd.X i) (Pp : DIV.Pl D.host.E) (d : List ℤ) (c : ℂ)
    (hc : ∀ Q : D.naut.AV i, D.naut.ptV i Q = some x → ∀ f' : D.what₂.Mt (D.nd.mu i) (j.1 + 1),
      (hj ▸ f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q → ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' (g * γ) = c • X.fn hμ j f' g) :
    ∀ m ∈ eigC D.nd D.naut i x, ∀ f' : D.what₂.Mt (D.nd.mu i) (j.1 + 1),
      (hj ▸ f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) = m → ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' (g * γ) = c • X.fn hμ j f' g := by
  intro m hm
  unfold eigC at hm
  refine Submodule.iSup_induction (fun Q => ⨆ (_ : Q ∈ {P | D.naut.ptV i P = some x}), D.naut.typeV i Q)
    (motive := fun m => ∀ f' : D.what₂.Mt (D.nd.mu i) (j.1 + 1),
      (hj ▸ f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) = m → ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' (g * γ) = c • X.fn hμ j f' g) hm ?_ ?_ ?_
  · intro Q m' hm' f' hf'
    by_cases hQ : D.naut.ptV i Q = some x
    · rw [iSup_pos (show Q ∈ {P | D.naut.ptV i P = some x} from hQ)] at hm'
      exact hc Q hQ f' (hf' ▸ hm')
    · rw [iSup_neg (show Q ∉ {P | D.naut.ptV i P = some x} from hQ), Submodule.mem_bot] at hm'
      have : f' = 0 := cast_inj hj (hf'.trans (hm'.trans (cast_zero hj).symm))
      subst this
      exact eig_zero X hμ j Pp d c
  · intro f' hf'
    have : f' = 0 := cast_inj hj (hf'.trans (cast_zero hj).symm)
    subst this
    exact eig_zero X hμ j Pp d c
  · intro m1 m2 ih1 ih2 f' hf'
    have hsplit : f' = (hj.symm ▸ m1 : D.what₂.Mt (D.nd.mu i) (j.1 + 1)) + (hj.symm ▸ m2) := by
      apply cast_inj hj
      rw [hf', cast_add, cast_symm, cast_symm]
    subst hsplit
    exact eig_add X hμ j Pp d c _ _ (ih1 _ (cast_symm hj m1)) (ih2 _ (cast_symm hj m2))

theorem placesOff : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), ∀ (i : D.nd.Loc), Formalism.IndefR.RecTie.Used0 D (D.nd.mu i) → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Pp ∉ D.nd.S i ∧ Pp ∉ D.nd.Q i := GlobalTheory.T.good_place_avoids_bad_sets

theorem summandEigen : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ (Q : D.naut.AV i), ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∃ c : ℂ, ∀ f' : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q → ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' (g * γ) = c • X.fn hμ j f' g := GlobalTheory.T.good_place_hecke_eigen_match

theorem eigenAgree : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ (x : D.nd.X i) (Q Q' : D.naut.AV i), D.naut.ptV i Q = some x → D.naut.ptV i Q' = some x → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → Pp ∉ D.nd.S i → Pp ∉ D.nd.Q i → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∀ f₁ f₂ : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f₁ : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q → (hj ▸ f₂ : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q' → f₁ ≠ 0 → f₂ ≠ 0 → ∀ c₁ c₂ : ℂ, (∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f₁ (g * γ) = c₁ • X.fn hμ j f₁ g) → (∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f₂ (g * γ) = c₂ • X.fn hμ j f₂ g) → c₁ = c₂ := GlobalTheory.T.points_equal_eigen_match

theorem uniform : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ (x : D.nd.X i) Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → Pp ∉ D.nd.S i → Pp ∉ D.nd.Q i → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∃ c : ℂ, ∀ Q : D.naut.AV i, D.naut.ptV i Q = some x → ∀ f' : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q → ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' (g * γ) = c • X.fn hμ j f' g := by
  intro hAF hL D P X hAg h41 h7 hTie i hμ j hj x Pp hG hS hPS hPQ d hd
  by_cases hex : ∃ (Q0 : D.naut.AV i) (f0 : D.what₂.Mt (D.nd.mu i) (j.1 + 1)), D.naut.ptV i Q0 = some x ∧
      (hj ▸ f0 : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q0 ∧ f0 ≠ 0
  · obtain ⟨Q0, f0, hQ0, hf0, hf00⟩ := hex
    obtain ⟨c0, hc0⟩ := summandEigen hAF hL D P X hAg h41 h7 hTie i hμ j hj Q0 Pp hG hS d hd
    refine ⟨c0, fun Q hQ f' hf' => ?_⟩
    obtain ⟨cQ, hcQ⟩ := summandEigen hAF hL D P X hAg h41 h7 hTie i hμ j hj Q Pp hG hS d hd
    by_cases hf'0 : f' = 0
    · subst hf'0; exact eig_zero X hμ j Pp d c0
    · have := eigenAgree hAF hL D P X hAg h41 h7 hTie i hμ j hj x Q0 Q hQ0 hQ Pp hG hS hPS hPQ d hd f0 f' hf0 hf'
        hf00 hf'0 c0 cQ (hc0 f0 hf0) (hcQ f' hf')
      rw [this]; exact hcQ f' hf'
  · refine ⟨0, fun Q hQ f' hf' => ?_⟩
    have hf'0 : f' = 0 := by
      by_contra hne; exact hex ⟨Q, f', hQ, hf', hne⟩
    subst hf'0; exact eig_zero X hμ j Pp d 0

theorem main : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∃ c : ℂ, h Pp (Finsupp.single d 1) y = c • y := by
  intro hAF hL D P X hAg h41 h7 hTie i hμ j hj x hx f hf y hy hy0 h hh Pp hG hS d hd
  have hA := placesOff hAF hL D P X hAg i hμ Pp hG
  have hu := uniform hAF hL D P X hAg h41 h7 hTie i hμ j hj x Pp hG hS hA.1 hA.2 d hd
  have hfE := alongEig X i hμ j hj x Pp d hu.choose hu.choose_spec _ hf f rfl
  refine ⟨hu.choose, transport X j _ h hh Pp hG d y hu.choose fun g => ?_⟩
  rw [hy]
  exact hfE g

end GlobalTheory.EigSplit
