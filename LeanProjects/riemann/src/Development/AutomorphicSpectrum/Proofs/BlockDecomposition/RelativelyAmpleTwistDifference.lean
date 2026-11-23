import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonzeroLocusSecMonoConst
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.FormalAlg

variable {X : Scheme.{0}}

theorem res_res_units {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (u : Γ(X, U)ˣ) :
    res h₂ (res h₁ u) = res (h₂.trans h₁) u :=
  Units.ext (resG_resG h₁ h₂ _)

theorem mul_chart_cancel {S : Type} [CommRing S] (u G k' k u' a : S) (h : u = G * k' * u') (h' : k' * k = 1) :
    u * (k * a) = G * (u' * a) := by
  subst h
  linear_combination (G * u' * a) * h'

theorem eq_of_resG_near {U : X.Opens} {a b : Γ(X, U)}
    (h : ∀ y ∈ U, ∃ (W : X.Opens) (_ : y ∈ W) (hW : W ≤ U), resG X hW a = resG X hW b) : a = b :=
  ext_germ fun y hy => by
    obtain ⟨W, hyW, hW, e⟩ := h y hy
    rw [← germ_resG hW y hyW a, ← germ_resG hW y hyW b, e]

theorem iso_sec_chart {A B : LB X} {w : LB.Iso A B} (hw : w.IsGen) (a : A.Sec) (p p' : B.ι) (q q' : A.ι)
    {W : X.Opens} (h₁ : W ≤ B.U p) (h₁' : W ≤ B.U p') (h₂ : W ≤ A.U q) (h₂' : W ≤ A.U q') :
    resG X (le_inf h₁ h₂) (@id (Γ(X, B.U p ⊓ A.U q)ˣ) (w.s (p, q)) : Γ(X, B.U p ⊓ A.U q)) * resG X h₂ (a.f q) =
      resG X (le_inf h₁ h₁') (B.g p p' : Γ(X, B.U p ⊓ B.U p')) *
        (resG X (le_inf h₁' h₂') (@id (Γ(X, B.U p' ⊓ A.U q')ˣ) (w.s (p', q')) : Γ(X, B.U p' ⊓ A.U q')) *
          resG X h₂' (a.f q')) := by
  have hW : W ≤ (LB.div B A).U (p, q) ⊓ (LB.div B A).U (p', q') :=
    le_inf (le_inf h₁ h₂) (le_inf h₁' h₂')
  have e := congrArg (res hW) (hw (p, q) (p', q'))
  have e₂ : res hW ((LB.div B A).g (p, q) (p', q')) =
      res (le_inf h₁ h₁') (B.g p p') * (res (le_inf h₂ h₂') (A.g q q'))⁻¹ := by
    exact (map_mul (res hW) _ _).trans (congrArg₂ (· * ·) (res_res_units _ _ _)
      ((map_inv (res hW) _).trans (congrArg (·⁻¹) (res_res_units _ _ _))))
  rw [map_mul, e₂, res_res_units, res_res_units] at e
  have e₃ := congrArg (fun u : Γ(X, W)ˣ => (u : Γ(X, W))) e
  simp only [Units.val_mul] at e₃
  rw [sec_compat a q q' h₂ h₂']
  have e₄ : ((res (le_inf h₂ h₂') (A.g q q'))⁻¹ : Γ(X, W)ˣ).val * resG X (le_inf h₂ h₂') (A.g q q' : Γ(X, A.U q ⊓ A.U q')) = 1 :=
    Units.inv_mul (res (le_inf h₂ h₂') (A.g q q'))
  exact mul_chart_cancel _ _ _ _ _ _ e₃ e₄

theorem exists_secMaps {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) {w : LB.Iso A B} (hw : w.IsGen) (a : A.Sec) :
    ∃ b : B.Sec, SecMaps w a b := by
  have hself : ∀ (p : B.ι) {W : X.Opens} (h : W ≤ B.U p),
      resG X (le_inf h h) (B.g p p : Γ(X, B.U p ⊓ B.U p)) = 1 := by
    intro p W h
    have e := congrArg (fun u : Γ(X, B.U p)ˣ => resG X h (u : Γ(X, B.U p))) (hB.g_self p)
    simp only [val_res, resG_resG, Units.val_one, map_one] at e
    exact e
  have glue : ∀ p : B.ι, ∃ b : Γ(X, B.U p), ∀ q : A.ι, resG X (inf_le_left : B.U p ⊓ A.U q ≤ B.U p) b =
      (@id (Γ(X, B.U p ⊓ A.U q)ˣ) (w.s (p, q)) : Γ(X, B.U p ⊓ A.U q)) *
        resG X (inf_le_right : B.U p ⊓ A.U q ≤ A.U q) (a.f q) := by
    intro p
    obtain ⟨b, hb, -⟩ := X.sheaf.existsUnique_gluing' (fun q : A.ι => B.U p ⊓ A.U q) (B.U p)
      (fun _ => homOfLE inf_le_left)
      (fun y hy => by
        obtain ⟨q, hq⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, A.U i by rw [hA.cover]; trivial)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨q, hy, hq⟩)
      (fun q => (@id (Γ(X, B.U p ⊓ A.U q)ˣ) (w.s (p, q)) : Γ(X, B.U p ⊓ A.U q)) *
        resG X (inf_le_right : B.U p ⊓ A.U q ≤ A.U q) (a.f q))
      (fun q q' => by
        have h₁ : B.U p ⊓ A.U q ⊓ (B.U p ⊓ A.U q') ≤ B.U p := inf_le_left.trans inf_le_left
        have h₂ : B.U p ⊓ A.U q ⊓ (B.U p ⊓ A.U q') ≤ A.U q := inf_le_left.trans inf_le_right
        have h₃ : B.U p ⊓ A.U q ⊓ (B.U p ⊓ A.U q') ≤ A.U q' := inf_le_right.trans inf_le_right
        have k := iso_sec_chart hw a p p q q' h₁ h₁ h₂ h₃
        rw [hself p h₁, one_mul] at k
        change resG X inf_le_left _ = resG X inf_le_right _
        rw [map_mul, map_mul]
        repeat rw [resG_resG]
        exact k)
    exact ⟨b, hb⟩
  choose b hb using glue
  refine ⟨⟨b, fun p p' => ?_⟩, fun r => hb r.1 r.2⟩
  refine eq_of_resG_near fun y hy => ?_
  obtain ⟨q, hq⟩ := TopologicalSpace.Opens.mem_iSup.1 (show y ∈ ⨆ i, A.U i by rw [hA.cover]; trivial)
  have h₀ : B.U p ⊓ B.U p' ⊓ A.U q ≤ B.U p ⊓ B.U p' := inf_le_left
  have h₁ : B.U p ⊓ B.U p' ⊓ A.U q ≤ B.U p := inf_le_left.trans inf_le_left
  have h₁' : B.U p ⊓ B.U p' ⊓ A.U q ≤ B.U p' := inf_le_left.trans inf_le_right
  have h₂ : B.U p ⊓ B.U p' ⊓ A.U q ≤ A.U q := inf_le_right
  refine ⟨B.U p ⊓ B.U p' ⊓ A.U q, ⟨hy, hq⟩, h₀, ?_⟩
  have e₁ := congrArg (resG X (le_inf h₁ h₂)) (hb p q)
  have e₂ := congrArg (resG X (le_inf h₁' h₂)) (hb p' q)
  rw [map_mul, resG_resG, resG_resG] at e₁ e₂
  have k := iso_sec_chart hw a p p' q q h₁ h₁' h₂ h₂
  change resG X h₀ (resG X inf_le_left (b p)) = resG X h₀ ((B.g p p' : Γ(X, B.U p ⊓ B.U p')) * resG X inf_le_right (b p'))
  rw [map_mul, resG_resG, resG_resG]
  exact e₁.trans (k.trans (congrArg _ e₂.symm))

theorem relAmple_tw_of_roots : ∀ (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R))) (Q : LB X.left) (m : ℕ) (ζ : Fin (m + 1) → LB.Sec Q), Q.IsLB → VeryAmpleBy X.hom Q ζ → ∀ (A C : LB X.left) (n : ℕ), 1 ≤ n → A.IsLB → C.IsLB → LBIso (pw A ((n + 1 : ℕ) : ℤ)) Q → LBIso (pw C (n : ℤ)) Q → RelAmple X (tw C A (-1)) := by
  intro R _ X Q m ζ hQ hva A C n hn hA hC hAQ hCQ
  have hM : (tw C A (-1)).IsLB := isLB_tw hC hA _
  have hD : 1 ≤ n * (n + 1) := Nat.mul_pos hn (Nat.succ_pos n)
  have hP := isLB_pw hM ((n * (n + 1) : ℕ) : ℤ)
  have hcls : GlobalTheory.CechPic.cls _ hP = GlobalTheory.CechPic.cls Q hQ := by
    have hc : GlobalTheory.CechPic.cls _ hM = GlobalTheory.CechPic.cls C hC - GlobalTheory.CechPic.cls A hA := by
      refine (GlobalTheory.CechPic.cls_div hC (isLB_pw hA _) hM).trans ?_
      rw [GlobalTheory.AmpleStabFinite.cls_pw hA]
      simp
    have e₁ : ((n + 1 : ℕ) : ℤ) • GlobalTheory.CechPic.cls A hA = GlobalTheory.CechPic.cls Q hQ :=
      (GlobalTheory.AmpleStabFinite.cls_pw hA _).symm.trans ((GlobalTheory.CechPic.cls_eq_iff _ _).2 hAQ)
    have e₂ : (n : ℤ) • GlobalTheory.CechPic.cls C hC = GlobalTheory.CechPic.cls Q hQ :=
      (GlobalTheory.AmpleStabFinite.cls_pw hC _).symm.trans ((GlobalTheory.CechPic.cls_eq_iff _ _).2 hCQ)
    rw [GlobalTheory.AmpleStabFinite.cls_pw hM, hc, smul_sub]
    have f₁ : ((n * (n + 1) : ℕ) : ℤ) • GlobalTheory.CechPic.cls C hC = ((n + 1 : ℕ) : ℤ) • GlobalTheory.CechPic.cls Q hQ := by
      rw [← e₂, smul_smul]; congr 1 <;> (push_cast; ring)
    have f₂ : ((n * (n + 1) : ℕ) : ℤ) • GlobalTheory.CechPic.cls A hA = (n : ℤ) • GlobalTheory.CechPic.cls Q hQ := by
      rw [← e₁, smul_smul]; congr 1 <;> (push_cast; ring)
    rw [f₁, f₂, ← sub_smul]
    simp
  obtain ⟨w, hw⟩ : LBIso Q (pw (tw C A (-1)) ((n * (n + 1) : ℕ) : ℤ)) := (GlobalTheory.CechPic.cls_eq_iff hQ hP).1 hcls.symm
  choose t ht using fun i => exists_secMaps hQ hP hw (ζ i)
  obtain ⟨hs, hci⟩ := (veryAmpleBy_iff X.hom ζ).1 hva
  have ht' := iSup_nonzeroLocus_of_secMaps hs hQ hP ht
  refine GlobalTheory.Unif.relAmple_of_veryAmpleBy hM hD t ((veryAmpleBy_iff X.hom t).2 ⟨ht', ?_⟩)
  rw [toProj_eq_of_secMaps hs ht' ht]
  exact hci

end GlobalTheory.CompanionTheory.FormalAlg
