import Development.EtaleCohomology.KummerTheory.LHCutGlue

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open LateralTheory.KummerTheory LateralTheory.KummerTheory.LHCut

namespace LateralTheory.KummerTheory.ExIsoPf

variable {Λ : Type} [CommRing Λ]

theorem d_zero_of {F : Cx Λ} {Y : Scheme.{0}} {n m : ℤ} (h : m = n + 1) (a : Sec (F.X n) Y)
    (ha : Sec.map (F.d n (n + 1)) a = 0) : Sec.map (F.d n m) a = 0 := by
  subst h; exact ha

theorem d_zero_of' {F : Cx Λ} {Y : Scheme.{0}} {n m : ℤ} (h : m = n + 1) (a : Sec (F.X n) Y)
    (ha : Sec.map (F.d n m) a = 0) : Sec.map (F.d n (n + 1)) a = 0 := by
  subst h; exact ha

theorem coneEx' {I J K : Cx Λ} {X S : Scheme.{0}} {r : ℕ → ℕ} {M : ℕ} {μ : Pair I J K} {p : X ⟶ S}
    {γ : ∀ a : ℕ, Fin (r a) → Sec (I.X (a : ℤ)) X} {N : ℕ} {j : ℤ} {U : Over S}
    (h : ConeEx M μ p γ N j U) (j₀ : ℤ) (hj : j₀ + 1 = j) (x : Cone J K p r M j U)
    (hx : cD μ p γ j (j + 1) rfl U x = 0) : ∃ y : Cone J K p r M j₀ U, cD μ p γ j₀ j hj U y = N • x := by
  obtain rfl : j₀ = j - 1 := by omega
  exact h x hx

theorem ker_part (hD : Dict) (hL : LhSec) (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) (i : ℤ) (r : ℕ → ℕ)
    (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i)
    (γ : ∀ a : ℕ, Fin (r a) → Sec ((res _ (tw q i)).X (a : ℤ)) X) (hγ : ∀ a s, IsCls (c a s) (γ a s)) (M N : ℕ) (j : ℤ)
    (U : Over S) (h0 : ConeEx M (mu q i) p γ N j U) (y : ∀ a : Fin (M + 1), Fin (r a) → Ht q (sch.obj U.left) ((j + 1) - ((a : ℕ) : ℤ)) 0)
    (hy : lh q p U.hom i r c M (j + 1) y = 0) : N • y = 0 := by
  have hC := clsMore_of hD
  choose b hb using fun (a : Fin (M + 1)) (s : Fin (r a)) =>
    (hD (ZMod q) (res _ (tw q 0)) U.left ((j + 1) - ((a : ℕ) : ℤ))).2.1 (y a s)
  have hlh := hL q p i r c γ hγ M (j + 1) U y b hb
  obtain ⟨k, hk⟩ := ((hC (ZMod q) (res _ (tw q i)) (pullback p U.hom) (j + 1)).2.2.2 j rfl _ _ _ _ hlh
    (hC (ZMod q) (res _ (tw q i)) (pullback p U.hom) (j + 1)).1).1 hy
  have hcl : cD (mu q i) p γ j (j + 1) rfl U (b, k) = 0 := by
    refine Prod.ext ?_ ?_
    · funext a s
      show ((a : ℕ) : ℤ).negOnePow • Sec.map _ (b a s) = 0
      rw [d_zero_of (by omega) _ ((hD (ZMod q) (res _ (tw q 0)) U.left _).2.2.1 _ _ (hb a s)).1, smul_zero]
    · show Phi (mu q i) p γ (j + 1) (j + 1) rfl U b - Sec.map _ k = 0
      rw [hk, sub_zero, sub_self]
  obtain ⟨y', hy'⟩ := h0 (b, k) hcl
  funext a s
  have e := congrArg (fun z => z.1 a s) hy'
  change ((a : ℕ) : ℤ).negOnePow • Sec.map _ (y'.1 a s) = N • b a s at e
  show N • y a s = 0
  refine ((hC (ZMod q) (res _ (tw q 0)) U.left ((j + 1) - ((a : ℕ) : ℤ))).2.2.2 ((j - 1) + 1 - ((a : ℕ) : ℤ))
    (by omega) _ _ _ _ ((hC _ _ _ _).2.1 N _ _ (hb a s)) (hC _ _ _ _).1).2 ⟨(((a : ℕ) : ℤ).negOnePow : ℤ) • y'.1 a s, ?_⟩
  rw [sub_zero, ← e, Units.smul_def]
  exact map_zsmul _ _ _

section Gen
variable {I J K : Cx Λ} {X S : Scheme.{0}} {r : ℕ → ℕ} {M : ℕ} (μ : Pair I J K) (p : X ⟶ S)
  (γ : ∀ a : ℕ, Fin (r a) → Sec (I.X (a : ℤ)) X)

theorem cD_fst (j j' : ℤ) (h : j + 1 = j') (U : Over S) (x : Cone J K p r M j U) :
    (cD μ p γ j j' h U x).1 = dS (j + 1) (j' + 1) x.1 := rfl

theorem cD_snd (j j' : ℤ) (h : j + 1 = j') (U : Over S) (x : Cone J K p r M j U) :
    (cD μ p γ j j' h U x).2 = Phi μ p γ (j + 1) j' h U x.1 - Sec.map (K.d j j') x.2 := rfl

theorem dS_zero (n m : ℤ) (U : Scheme.{0}) : dS n m (0 : FinalTheorems J r M n U) = 0 := by
  funext a s
  simp [dS]

theorem Phi_zero (n w : ℤ) (h : n = w) (U : Over S) : Phi μ p γ n w h U (0 : FinalTheorems J r M n U.left) = 0 := by
  simp [Phi]

theorem closed_of_dS (n m : ℤ) (hm : m = n + 1) (U : Scheme.{0}) (b : FinalTheorems J r M n U) (hb : dS n m b = 0)
    (a : Fin (M + 1)) (s : Fin (r a)) : Sec.map (J.d (n - ((a : ℕ) : ℤ)) (n - ((a : ℕ) : ℤ) + 1)) (b a s) = 0 := by
  have e := congrFun (congrFun hb a) s
  simp only [dS, Pi.zero_apply] at e
  rw [smul_eq_zero_iff_eq] at e
  exact d_zero_of' (by omega) _ e

end Gen

theorem cok_part (hD : Dict) (hL : LhSec) (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) (i : ℤ) (r : ℕ → ℕ)
    (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i)
    (γ : ∀ a : ℕ, Fin (r a) → Sec ((res _ (tw q i)).X (a : ℤ)) X) (hγ : ∀ a s, IsCls (c a s) (γ a s)) (M N : ℕ) (j : ℤ)
    (U : Over S) (h1 : ConeEx M (mu q i) p γ N (j + 1) U) (b0 : Ht q (sch.obj (pullback p U.hom)) (j + 1) i) :
    ∃ y, lh q p U.hom i r c M (j + 1) y = N • b0 := by
  have hC := clsMore_of hD
  obtain ⟨k0, hk0⟩ := (hD (ZMod q) (res _ (tw q i)) (pullback p U.hom) (j + 1)).2.1 b0
  have hk0c := ((hD (ZMod q) (res _ (tw q i)) (pullback p U.hom) (j + 1)).2.2.1 _ _ hk0).1
  have hcl : cD (mu q i) p γ (j + 1) (j + 1 + 1) rfl U ((0, k0) : Cone _ _ p r M (j + 1) U) = 0 := by
    refine Prod.ext ?_ ?_
    · rw [cD_fst, dS_zero, Prod.fst_zero]
    · rw [cD_snd, Phi_zero, hk0c, sub_zero, Prod.snd_zero]
  obtain ⟨y', hy'⟩ := coneEx' h1 j rfl _ hcl
  have e1 := congrArg Prod.fst hy'
  rw [cD_fst, Prod.smul_fst, smul_zero] at e1
  have hcls := closed_of_dS (j + 1) (j + 1 + 1) rfl U.left y'.1 e1
  choose yc hyc using fun (a : Fin (M + 1)) (s : Fin (r a)) =>
    (hD (ZMod q) (res _ (tw q 0)) U.left ((j + 1) - ((a : ℕ) : ℤ))).1 (y'.1 a s) (hcls a s)
  refine ⟨yc, ?_⟩
  have hlh := hL q p i r c γ hγ M (j + 1) U yc y'.1 hyc
  refine ((hC (ZMod q) (res _ (tw q i)) (pullback p U.hom) (j + 1)).2.2.2 j rfl _ _ _ _ hlh
    ((hC _ _ _ _).2.1 N _ _ hk0)).2 ⟨y'.2, ?_⟩
  have e2 := congrArg Prod.snd hy'
  rw [cD_snd, Prod.smul_snd] at e2
  rw [← e2, sub_sub_cancel]

theorem exIso_of (hD : Dict) (hL : LhSec) : ExIso := by
  intro q X S p i r c γ hγ M N j U h0 h1
  exact ⟨fun y hy => ker_part hD hL q p i r c γ hγ M N j U h0 y hy, cok_part hD hL q p i r c γ hγ M N j U h1⟩

end LateralTheory.KummerTheory.ExIsoPf

end
