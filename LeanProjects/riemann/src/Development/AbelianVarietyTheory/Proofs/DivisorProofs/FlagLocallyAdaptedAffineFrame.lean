import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSecOn
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB GlobalTheory.FlagZ GlobalTheory

set_option autoImplicit false
noncomputable section

open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (appLinear appLinear_apply injective_app_of_mono exact_app_of_exact_of_mono)

namespace GlobalTheory.FlagZ.Loc

theorem isFrame_snoc_of_exact {X : Scheme.{0}} {U : X.Opens}
    {S : ShortComplex X.Modules} (hS : S.Exact) [Mono S.f] {m : ℕ}
    (a : Fin m → Γ(S.X₁, U)) (b : Γ(S.X₂, U)) (ha : IsFrame a)
    (hb : IsFrame fun _ : Fin 1 => S.g.app U b) :
    IsFrame (Fin.snoc (fun i => S.f.app U (a i)) b : Fin (m + 1) → Γ(S.X₂, U)) := by
  intro V h
  have hex := exact_app_of_exact_of_mono hS V
  have hlc : ∀ c : Fin (m + 1) → Γ(X, V),
      Fintype.linearCombination Γ(X, V) (fun i => resM S.X₂ h
        ((Fin.snoc (fun i => S.f.app U (a i)) b : Fin (m + 1) → Γ(S.X₂, U)) i)) c =
      appLinear S.f V (Fintype.linearCombination Γ(X, V) (fun i => resM S.X₁ h (a i))
        (fun i => c i.castSucc)) + c (Fin.last m) • resM S.X₂ h b := by
    intro c
    simp only [Fintype.linearCombination_apply, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
      Fin.snoc_last, map_sum, map_smul, appLinear_apply, app_resM]
  have hb1 : ∀ y : Γ(X, V), Fintype.linearCombination Γ(X, V)
      (fun i : Fin 1 => resM S.X₃ h ((fun _ : Fin 1 => S.g.app U b) i)) (fun _ => y) =
      appLinear S.g V (y • resM S.X₂ h b) := by
    intro y
    simp [Fintype.linearCombination_apply, appLinear_apply, app_resM]
  refine ⟨(injective_iff_map_eq_zero _).2 fun c hc => ?_, fun s => ?_⟩
  · rw [hlc] at hc
    have h1 := congrArg (appLinear S.g V) hc
    rw [map_add, appLinear_apply S.f, appLinear_apply S.g, hex.apply_apply_eq_zero, zero_add,
      map_zero, ← hb1] at h1
    have h2 : (fun _ : Fin 1 => c (Fin.last m)) = 0 :=
      (injective_iff_map_eq_zero _).1 (hb V h).1 _ h1
    have hl : c (Fin.last m) = 0 := congrFun h2 0
    rw [hl, zero_smul, add_zero, appLinear_apply] at hc
    have h3 := (injective_iff_map_eq_zero _).1 (ha V h).1 _
      (injective_app_of_mono S.f V (hc.trans (map_zero _).symm))
    funext i
    refine Fin.lastCases hl (fun j => congrFun h3 j) i
  · obtain ⟨y, hy⟩ := (hb V h).2 (S.g.app V s)
    have hy' : Fintype.linearCombination Γ(X, V)
        (fun i : Fin 1 => resM S.X₃ h ((fun _ : Fin 1 => S.g.app U b) i)) (fun _ => y 0) =
        S.g.app V s := by
      rw [← hy]; congr 1; funext i; rw [Fin.fin_one_eq_zero i]
    rw [hb1, appLinear_apply] at hy'
    obtain ⟨x, hx⟩ := (hex (s - y 0 • resM S.X₂ h b)).1
      (by rw [map_sub, ← hy', sub_self])
    obtain ⟨c, hc⟩ := (ha V h).2 x
    refine ⟨Fin.snoc c (y 0), ?_⟩
    rw [hlc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [show (fun i => c i) = c from rfl, hc, appLinear_apply, hx, sub_add_cancel]

theorem exists_nested_frames {X : Scheme.{0}} {E : X.Modules} {N : ℕ} (fl : Vert.Flag E N)
    (t : X) (k : Fin (N + 1)) :
    ∃ V : X.Opens, t ∈ V ∧ ∃ u : Fin k → Γ(fl.F k, V), IsFrame u ∧
      ∀ (l : Fin (N + 1)) (hl : (l : ℕ) ≤ k), ∃ s : Fin l → Γ(fl.F l, V), IsFrame s ∧
        ∀ j, (fl.ι l).app V (s j) = (fl.ι k).app V (u (Fin.castLE hl j)) := by
  induction k using Fin.induction with
  | zero =>
    obtain ⟨V, e, ht, he⟩ := fl.isVB 0 t
    refine ⟨V, ht, e, he, fun l hl => ?_⟩
    obtain rfl : l = 0 := Fin.ext (by simpa using hl)
    exact ⟨e, he, fun j => rfl⟩
  | succ i ih =>
    obtain ⟨V, htV, u, hu, hs⟩ := ih
    obtain ⟨U', c, htU', hc⟩ := fl.isVB_gr i t
    obtain ⟨W, hW, htW, b, hb⟩ := exists_app_eq_of_epi (fl.π i)
      (resM _ (inf_le_right : V ⊓ U' ≤ U') (c 0)) (show t ∈ V ⊓ U' from ⟨htV, htU'⟩)
    have hWV : W ≤ V := hW.trans inf_le_left
    let S := ShortComplex.mk (fl.step i) (fl.π i) (Limits.cokernel.condition _)
    have hS : S.Exact := ShortComplex.exact_cokernel (fl.step i)
    have hbf : IsFrame fun _ : Fin 1 => S.g.app W b := by
      convert hc.res (hW.trans inf_le_right) using 1
      funext j
      rw [Fin.fin_one_eq_zero j]
      exact hb.trans (resM_resM _ _ _)
    have hstep : ∀ x, (fl.ι i.succ).app W ((fl.step i).app W x) = (fl.ι i.castSucc).app W x :=
      fun x => (QCoh.app_app _ _ _ _).trans (by rw [fl.step_ι])
    refine ⟨W, htW, Fin.snoc (fun j => (fl.step i).app W (resM _ hWV (u j))) b,
      isFrame_snoc_of_exact (S := S) hS _ b (hu.res hWV) hbf, fun l hl => ?_⟩
    by_cases heq : (l : ℕ) = i.succ
    · obtain rfl : l = i.succ := Fin.ext heq
      exact ⟨_, isFrame_snoc_of_exact (S := S) hS _ b (hu.res hWV) hbf, fun j => rfl⟩
    · have hl' : (l : ℕ) ≤ i.castSucc := by
        simp only [Fin.val_succ, Fin.val_castSucc] at hl heq ⊢; omega
      obtain ⟨s, hsf, hsj⟩ := hs l hl'
      refine ⟨fun j => resM _ hWV (s j), hsf.res hWV, fun j => ?_⟩
      rw [app_resM (fl.ι l) hWV, hsj j, ← app_resM]
      show _ = (fl.ι i.succ).app W ((Fin.snoc (fun j => (fl.step i).app W (resM _ hWV (u j))) b :
        Fin ((i.castSucc : ℕ) + 1) → Γ(fl.F i.succ, W)) (Fin.castSucc (Fin.castLE hl' j)))
      rw [Fin.snoc_castSucc, hstep]

theorem isFrame_stdSec {N : ℕ} {T : Scheme.{0}} (g : T ⟶ Sp ℤ) (V : T.Opens) :
    IsFrame fun i : Fin N => QCoh.pullbackSections g (Taut.stdE N) (by simp : V ≤ g ⁻¹ᵁ ⊤)
      (freeFrame (Sp ℤ) (Fin N) i) := by
  haveI : (Taut.stdE N).IsQuasicoherent := (isVB_freeModule_fin (Sp ℤ) N).isQuasicoherent
  have := ((isFrame_freeFrame (Sp ℤ) (Fin N)).pullback g).res (by simp : V ≤ g ⁻¹ᵁ ⊤)
  rw [show (fun i : Fin N => QCoh.pullbackSections g (Taut.stdE N) (by simp : V ≤ g ⁻¹ᵁ ⊤)
      (freeFrame (Sp ℤ) (Fin N) i)) = fun i => resM _ (by simp : V ≤ g ⁻¹ᵁ ⊤)
      (QCoh.pullbackSections g (Taut.stdE N) le_rfl (freeFrame (Sp ℤ) (Fin N) i)) from
      funext fun i => (QCoh.res_pullbackSections _ _ _ _ _).symm]
  exact this

theorem exists_GL_colSecOn {N : ℕ} {T : Scheme.{0}} (g : T ⟶ Sp ℤ) (V : T.Opens)
    (v : Fin N → Γ((Scheme.Modules.pullback g).obj (Taut.stdE N), V)) (hv : IsFrame v) :
    ∃ G : GL (Fin N) Γ(T, V), ∀ j, colSecOn g V G.1 j = v j := by
  classical
  have he := isFrame_stdSec (N := N) g V
  letI := (he.basis le_rfl).invertibleToMatrix (hv.basis le_rfl)
  refine ⟨unitOfInvertible ((he.basis le_rfl).toMatrix (hv.basis le_rfl)), fun j => ?_⟩
  have := (he.basis le_rfl).sum_toMatrix_smul_self (hv.basis le_rfl) j
  simp only [IsFrame.basis_apply, resM_self] at this
  rw [val_unitOfInvertible]
  exact this

theorem resM_colSecOn {N : ℕ} {T : Scheme.{0}} (g : T ⟶ Sp ℤ) {V W : T.Opens} (h : W ≤ V)
    (M : Matrix (Fin N) (Fin N) Γ(T, V)) (j : Fin N) :
    resM _ h (colSecOn g V M j) = colSecOn g W (M.map (resG T h)) j := by
  simp only [colSecOn, map_sum, resM_smul, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => congrArg _ ?_
  exact QCoh.res_pullbackSections _ _ _ _ _

theorem exists_adapted : ∀ {ι : Type} [Fintype ι] {N : ℕ} {T : Scheme.{0}} (g : T ⟶ Sp ℤ)
    (fl' : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback g).obj (Taut.stdE N)) N) (t : T),
    ∃ V : T.Opens, t ∈ V ∧ IsAffineOpen V ∧ ∃ G : ι → GL (Fin N) Γ(T, V), Loc.Adapted g fl' V G := by
  intro ι _ N T g fl' t
  have one : ∀ a, ∃ V : T.Opens, t ∈ V ∧ ∃ G : GL (Fin N) Γ(T, V), ∀ l : Fin (N + 1),
      ∃ s : Fin l → Γ((fl' a).F l, V), IsFrame s ∧
        ∀ j, ((fl' a).ι l).app V (s j) = colSecOn g V G.1 (Fin.castLE l.is_le j) := by
    intro a
    obtain ⟨V, htV, u, hu, hs⟩ := exists_nested_frames (fl' a) t (Fin.last N)
    obtain ⟨G, hG⟩ := exists_GL_colSecOn g V (fun j => ((fl' a).ι (Fin.last N)).app V (u j))
      (hu.map_iso _)
    refine ⟨V, htV, G, fun l => ?_⟩
    obtain ⟨s, hsf, hsj⟩ := hs l l.is_le
    exact ⟨s, hsf, fun j => (hsj j).trans (hG _).symm⟩
  choose V htV G hG using one
  have ht0 : t ∈ Finset.univ.inf V := by
    rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_finset_inf]
    simpa using htV
  obtain ⟨W, hW, htW, hle⟩ := QCoh.exists_affine_mem_le t ht0
  have hWa (a : ι) : W ≤ V a := hle.trans (Finset.inf_le (Finset.mem_univ a))
  refine ⟨W, htW, hW, fun a => Units.map (RingHom.mapMatrix (resG T (hWa a))).toMonoidHom (G a),
    fun a l => ?_⟩
  obtain ⟨s, hsf, hsj⟩ := hG a l
  refine ⟨fun j => resM _ (hWa a) (s j), hsf.res (hWa a), fun j => ?_⟩
  dsimp only
  rw [app_resM, hsj, resM_colSecOn]
  rfl

end GlobalTheory.FlagZ.Loc
