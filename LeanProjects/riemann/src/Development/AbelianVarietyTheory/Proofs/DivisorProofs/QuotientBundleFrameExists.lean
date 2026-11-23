import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM resM_resM resM_smul app_resM sec_ext_of_cover)
open GlobalTheory.LB (exists_fun_of_cover)

namespace GlobalTheory.VB.CokerFrame

variable {X : Scheme.{0}} {F : X.Modules} {U : X.Opens} {ι : Type} [Fintype ι]

theorem isFrame_of_injective_of_local {e : ι → Γ(F, U)}
    (inj : ∀ (V : X.Opens) (h : V ≤ U),
      Function.Injective (Fintype.linearCombination Γ(X, V) fun i => resM F h (e i)))
    (loc : ∀ (V : X.Opens) (h : V ≤ U) (s : Γ(F, V)) (x : X), x ∈ V →
      ∃ (W : X.Opens) (h' : W ≤ V), x ∈ W ∧ ∃ a : ι → Γ(X, W),
        Fintype.linearCombination Γ(X, W) (fun i => resM F (h'.trans h) (e i)) a = resM F h' s) :
    VB.IsFrame e := by
  refine fun V h => ⟨inj V h, fun s => ?_⟩
  choose W hW hx a ha using fun x : V => loc V h s x x.2
  have hc : V ≤ iSup W := fun x hxV => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxV⟩, hx _⟩
  have key (x y : V) : (fun i => resG X (inf_le_left : W x ⊓ W y ≤ W x) (a x i)) =
      fun i => resG X (inf_le_right : W x ⊓ W y ≤ W y) (a y i) := by
    apply inj _ (inf_le_left.trans ((hW x).trans h))
    rw [← VB.resM_linearCombination e ((hW x).trans h), ← VB.resM_linearCombination e ((hW y).trans h),
      ha, ha, resM_resM, resM_resM]
  choose b hb' using fun i => exists_fun_of_cover W hW hc (fun x => a x i)
    fun x y => congrFun (key x y) i
  refine ⟨b, sec_ext_of_cover W hW hc fun x => ?_⟩
  rw [VB.resM_linearCombination, ← ha x]
  exact congrArg _ (funext fun i => hb' i x)

theorem sum_eq_sum_last {M : Type*} [AddCommMonoid M] {N l : ℕ} (hl : l ≤ N) (g : Fin N → M)
    (hg : ∀ j : Fin N, (j : ℕ) < l → g j = 0) :
    ∑ j, g j = ∑ k : Fin (N - l), g ⟨l + k, by omega⟩ := by
  symm
  refine Finset.sum_of_injOn (fun k : Fin (N - l) => (⟨l + k, by omega⟩ : Fin N))
    (fun a _ b _ hab => ?_) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) (fun j _ hj => ?_)
    (fun _ _ => rfl)
  · have := congrArg Fin.val hab
    simp only at this
    exact Fin.ext (by omega)
  · refine hg j (Nat.lt_of_not_le fun hlj => hj ⟨⟨j - l, by omega⟩, by simp, Fin.ext ?_⟩)
    simp only
    omega

end GlobalTheory.VB.CokerFrame

open GlobalTheory.VB.CokerFrame in

theorem GlobalTheory.VB.exists_isFrame_cokernel_of_frame :
    ∀ {X : Scheme.{0}} {F : X.Modules} {U : X.Opens} {N : ℕ} (P : VB.Sub F) (c : Fin N → Γ(F, U)),
      VB.IsFrame c → ∀ (l : ℕ), l ≤ N →
      (∀ (V : X.Opens) (h : V ≤ U) (a : Fin N → Γ(X, V)),
        (∑ j, a j • resM F h (c j)) ∈ P.sec V ↔ ∀ j : Fin N, l ≤ (j : ℕ) → a j = 0) →
      ∃ e : Fin (N - l) → Γ(cokernel P.incl, U), VB.IsFrame e := by
  intro X F U N P c hc l hl hP
  set π := cokernel.π P.incl

  have hlow (V : X.Opens) (h : V ≤ U) (j : Fin N) (hj : (j : ℕ) < l) :
      π.app V (resM F h (c j)) = 0 := by
    classical
    rw [VB.Sub.cokernel_π_app_eq_zero_iff]
    have := (hP V h (Pi.single j 1)).2 fun j' hj' => by
      rw [Pi.single_apply, if_neg (fun e => by subst e; omega)]
    simpa [Pi.single_apply] using this
  refine ⟨fun k => π.app U (c ⟨l + k, by omega⟩), isFrame_of_injective_of_local ?_ ?_⟩
  · intro V h
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    classical
    let b : Fin N → Γ(X, V) := fun j => if hj : l ≤ (j : ℕ) then a ⟨j - l, by omega⟩ else 0
    have hsum : (∑ j, b j • resM F h (c j)) =
        ∑ k : Fin (N - l), a k • resM F h (c ⟨l + k, by omega⟩) := by
      rw [sum_eq_sum_last hl]
      · refine Finset.sum_congr rfl fun k _ => ?_
        simp only [b, dif_pos (Nat.le_add_right l k)]
        congr 2
        ext
        simp
      · intro j hj
        simp only [b, dif_neg (by omega : ¬ l ≤ (j : ℕ)), zero_smul]
    have hmem : (∑ j, b j • resM F h (c j)) ∈ P.sec V := by
      rw [hsum, ← VB.Sub.cokernel_π_app_eq_zero_iff]
      rw [Fintype.linearCombination_apply] at ha
      rw [map_sum]
      simpa only [Scheme.Modules.Hom.app_smul, app_resM] using ha
    have hb := (hP V h b).1 hmem
    funext k
    have := hb ⟨l + k, by omega⟩ (Nat.le_add_right l k)
    simpa [b] using this
  · intro V h t x hx
    obtain ⟨W, h', hxW, s, hs⟩ := VB.exists_app_eq_of_epi π t hx
    obtain ⟨β, hβ⟩ := (hc W (h'.trans h)).2 s
    refine ⟨W, h', hxW, fun k => β ⟨l + k, by omega⟩, ?_⟩
    rw [← hs, ← hβ, Fintype.linearCombination_apply, Fintype.linearCombination_apply, map_sum,
      sum_eq_sum_last hl]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [Scheme.Modules.Hom.app_smul, app_resM]
    · intro j hj
      rw [Scheme.Modules.Hom.app_smul, hlow W (h'.trans h) j hj, smul_zero]
