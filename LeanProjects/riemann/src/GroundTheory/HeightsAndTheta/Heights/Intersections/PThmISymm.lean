import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsWellDefined
import GroundTheory.HeightsAndTheta.Heights.Intersections.ThmIExistsFamily
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChoice
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotLtLtOfMemMinimalPrimes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

namespace ThmISymm

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem smooth_snoc {n : ℕ} {L : Fin n → HermLine ι} {X : HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    (hX : IsSmoothHerm X) : ∀ j, IsSmoothHerm ((Fin.snoc L X : Fin (n + 1) → HermLine ι) j) := by
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simpa using hX
  · simpa using hL j

theorem geoNum_comp_perm
    (hEU : ∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement (ZMod p) ι)
    (hSy : ∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.AI.I1.SymmStatement (ZMod p) ι)
    (hGN : ReciprocityTheory.ChartRestriction.G.AI.I1.GeoNumStatement ι) (hFC : FibreCompStatement)
    {P : Ideal (MRing ι)} {n : ℕ} {A : HermLine ι} {s : MRing ι} {W : Ideal (MRing ι)}
    (hP : IsArithVar P (n + 1)) (hs : IsSectionOn P A s) (hW : W ∈ divSupp P s)
    (hv : ¬ IsHorizontal W) (a : Fin n → K → ℤ) (τ : Equiv.Perm (Fin n)) :
    geoNum n W (a ∘ τ) = geoNum n W a := by
  obtain ⟨hp, hpW, hWm, hWv⟩ := hFC K ι P n A s W hP hs hW hv
  have : Fact (charOf W).Prime := ⟨hp⟩
  obtain ⟨I, hI, -⟩ := hEU (charOf W)
  rw [hGN (charOf W) I hI W n (a ∘ τ) hWm hpW hWv, hGN (charOf W) I hI W n a hWm hpW hWv]
  exact hSy (charOf W) I hI _ n a τ hWv

theorem recR_comp_perm
    (hEU : ∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement (ZMod p) ι)
    (hSy : ∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.AI.I1.SymmStatement (ZMod p) ι)
    (hGN : ReciprocityTheory.ChartRestriction.G.AI.I1.GeoNumStatement ι) (hFC : FibreCompStatement)
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) {P : Ideal (MRing ι)} {n : ℕ}
    (hP : IsArithVar P (n + 1)) (L : Fin n → HermLine ι) (B : HermLine ι) {s : MRing ι}
    (hs : IsSectionOn P B s) (τ : Equiv.Perm (Fin n))
    (hI : ∀ W, IsArithVar W n → I W n (L ∘ τ) = I W n L) :
    recR I P (L ∘ τ) B s = recR I P L B s := by
  unfold recR
  congr 1
  · refine finsum_mem_congr rfl fun W hW => ?_
    congr 1
    split_ifs with hh
    · exact hI W ((divSuppArith K ι P n B s W hP hs hW).1 hh)
    · have h := geoNum_comp_perm hEU hSy hGN hFC hP hs hW hh (fun j => (L j).a) τ
      have h' : geoNum n W (fun j => ((L ∘ τ) j).a) = geoNum n W (fun j => (L j).a) := h
      rw [h']
  · exact ptsIntegral_comp_perm P (fun j z => Real.log ((L j).h z)) τ _

section Main

variable (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)

theorem rAt (hR : IsRFamily I) {P : Ideal (MRing ι)} {n : ℕ} {L : Fin n → HermLine ι} {A : HermLine ι}
    {s : MRing ι} (hP : IsArithVar P (n + 1)) (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hs : IsSectionOn P A s) : I P (n + 1) (Fin.snoc L A) = recR I P L A s := by
  obtain ⟨a, ha, has, hsP⟩ := hs
  exact hR.2 P n L A s a hP hL hA ha has hsP

theorem lastFix
    (hEU : ∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement (ZMod p) ι)
    (hSy : ∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.AI.I1.SymmStatement (ZMod p) ι)
    (hGN : ReciprocityTheory.ChartRestriction.G.AI.I1.GeoNumStatement ι) (hFC : FibreCompStatement)
    (hR : IsRFamily I) {P : Ideal (MRing ι)} {m : ℕ} (hP : IsArithVar P (m + 1 + 1))
    (ih : ∀ W, IsArithVar W (m + 1) → ∀ L : Fin (m + 1) → HermLine ι, (∀ j, IsSmoothHerm (L j)) →
      ∀ τ : Equiv.Perm (Fin (m + 1)), I W (m + 1) (L ∘ τ) = I W (m + 1) L)
    (L : Fin (m + 1) → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) (A : HermLine ι) (hA : IsSmoothHerm A)
    (τ : Equiv.Perm (Fin (m + 1))) :
    I P (m + 1 + 1) (Fin.snoc (L ∘ τ) A) = I P (m + 1 + 1) (Fin.snoc L A) := by
  set H : HermLine ι := ThmIExists.segreLine (ThmIExists.shift A)
  have hH : IsSmoothHerm H := ThmIExists.isSmoothHerm_segreLine _
  have ht := ThmIExists.isSectionOn_up hP A
  have hu := ThmIExists.isSectionOn_segre hP (ThmIExists.shift A)
  have key : ∀ L' : Fin (m + 1) → HermLine ι, (∀ j, IsSmoothHerm (L' j)) →
      I P (m + 1 + 1) (Fin.snoc L' A) =
        recR I P L' (A.tensor H) (ThmIExists.secOf P (ThmIExists.upDeg A)) -
          recR I P L' H (ThmIExists.secOf P fun _ => ThmIExists.shift A) := by
    intro L' hL'
    have h1 := hR.1 P (m + 1) L' A H hP hL' hA hH
    rw [rAt I hR hP hL' (ThmIExists.smooth_tensor hA hH) ht, rAt I hR hP hL' hH hu] at h1
    linarith
  rw [key (L ∘ τ) (fun j => hL (τ j)), key L hL,
    recR_comp_perm hEU hSy hGN hFC I hP L _ ht τ (fun W hW => ih W hW L hL τ),
    recR_comp_perm hEU hSy hGN hFC I hP L _ hu τ (fun W hW => ih W hW L hL τ)]

theorem addX_sec (hR : IsRFamily I) (hRS : RPositionAdd.Statement) {P : Ideal (MRing ι)} {m : ℕ}
    (hP : IsArithVar P (m + 1 + 1)) {L : Fin m → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    {A C Y : HermLine ι} (hA : IsSmoothHerm A) (hC : IsSmoothHerm C) (hY : IsSmoothHerm Y) {y : MRing ι}
    (hy : IsSectionOn P Y y) :
    I P (m + 1 + 1) (Fin.snoc (Fin.snoc L (A.tensor C)) Y) =
      I P (m + 1 + 1) (Fin.snoc (Fin.snoc L A) Y) + I P (m + 1 + 1) (Fin.snoc (Fin.snoc L C) Y) := by
  rw [rAt I hR hP (smooth_snoc hL (ThmIExists.smooth_tensor hA hC)) hY hy,
    rAt I hR hP (smooth_snoc hL hA) hY hy, rAt I hR hP (smooth_snoc hL hC) hY hy]
  exact hRS K ι I P m L A C Y y (fun W L' A' C' hW hL' hA' hC' => hR.1 W m L' A' C' hW hL' hA' hC')
    hP hL hA hC hY hy

theorem addX (hR : IsRFamily I) (hRS : RPositionAdd.Statement) {P : Ideal (MRing ι)} {m : ℕ}
    (hP : IsArithVar P (m + 1 + 1)) {L : Fin m → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    {A C Y : HermLine ι} (hA : IsSmoothHerm A) (hC : IsSmoothHerm C) (hY : IsSmoothHerm Y) :
    I P (m + 1 + 1) (Fin.snoc (Fin.snoc L (A.tensor C)) Y) =
      I P (m + 1 + 1) (Fin.snoc (Fin.snoc L A) Y) + I P (m + 1 + 1) (Fin.snoc (Fin.snoc L C) Y) := by
  set H : HermLine ι := ThmIExists.segreLine (ThmIExists.shift Y)
  have hH : IsSmoothHerm H := ThmIExists.isSmoothHerm_segreLine _
  have ht := ThmIExists.isSectionOn_up hP Y
  have hu := ThmIExists.isSectionOn_segre hP (ThmIExists.shift Y)
  have e : ∀ Z, IsSmoothHerm Z → I P (m + 1 + 1) (Fin.snoc (Fin.snoc L Z) (Y.tensor H)) =
      I P (m + 1 + 1) (Fin.snoc (Fin.snoc L Z) Y) + I P (m + 1 + 1) (Fin.snoc (Fin.snoc L Z) H) :=
    fun Z hZ => hR.1 P (m + 1) (Fin.snoc L Z) Y H hP (smooth_snoc hL hZ) hY hH
  have h1 := addX_sec I hR hRS hP hL hA hC (ThmIExists.smooth_tensor hY hH) ht
  have h2 := addX_sec I hR hRS hP hL hA hC hH hu
  have e1 := e _ (ThmIExists.smooth_tensor hA hC)
  have e2 := e A hA
  have e3 := e C hC
  linarith

theorem swap_sec (hR : IsRFamily I) (hSwap : Swap.Statement) {P : Ideal (MRing ι)} {m : ℕ}
    (hP : IsArithVar P (m + 1 + 1)) {L : Fin m → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    {X Y : HermLine ι} (hX : IsSmoothHerm X) (hY : IsSmoothHerm Y) {x y : MRing ι}
    (hx : IsSectionOn P X x) (hy : IsSectionOn P Y y) (hd : ∀ W, W ∈ divSupp P y → W ∉ divSupp P x) :
    I P (m + 1 + 1) (Fin.snoc (Fin.snoc L X) Y) = I P (m + 1 + 1) (Fin.snoc (Fin.snoc L Y) X) := by
  rw [rAt I hR hP (smooth_snoc hL hX) hY hy, rAt I hR hP (smooth_snoc hL hY) hX hx]
  exact hSwap K ι I P m L Y X y x (fun P' L' A' s' hP' hL' hA' hs' => rAt I hR hP' hL' hA' hs')
    hP hL hY hX hy hx hd

theorem swap_half (hR : IsRFamily I) (hRS : RPositionAdd.Statement) (hSwap : Swap.Statement)
    {P : Ideal (MRing ι)} {m : ℕ} (hP : IsArithVar P (m + 1 + 1)) {L : Fin m → HermLine ι}
    (hL : ∀ j, IsSmoothHerm (L j)) {X Y : HermLine ι} (hX : IsSmoothHerm X) (hY : IsSmoothHerm Y)
    {y : MRing ι} (hy : IsSectionOn P Y y) :
    I P (m + 1 + 1) (Fin.snoc (Fin.snoc L X) Y) = I P (m + 1 + 1) (Fin.snoc (Fin.snoc L Y) X) := by
  classical
  set S : Set (Ideal (MRing ι)) := insert P (divSupp P y)
  have hS : S.Finite := (divSupp_finite P y).insert P
  have hS' : ∀ W ∈ S, IsMultiProjPrime W := by
    rintro W (rfl | hW)
    · exact hP.2.1
    · by_cases hh : IsHorizontal W
      · exact ((divSuppArith K ι P (m + 1) Y y W hP hy hW).1 hh).2.1
      · exact ((divSuppArith K ι P (m + 1) Y y W hP hy hW).2 hh).1
  obtain ⟨d₀, hd₀⟩ := Choice.exists_form_avoid (R := ℤ) S hS hS'
  set k : ℕ := ThmIExists.shift X + ∑ l, d₀ l
  set HK : HermLine ι := ThmIExists.segreLine k
  have hHK : IsSmoothHerm HK := ThmIExists.isSmoothHerm_segreLine k
  have hle : ∀ l, d₀ l ≤ ∑ l, d₀ l := fun l =>
    Finset.single_le_sum (f := d₀) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
  have habs : ∀ l, (X.a l).natAbs ≤ ThmIExists.shift X := fun l =>
    Finset.single_le_sum (f := fun l => (X.a l).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
  have hnn : ∀ l, (d₀ l : ℤ) ≤ X.a l + k := fun l => by
    have h1 := hle l
    have h2 := habs l
    omega
  set b : K → ℕ := fun l => (X.a l + k).toNat
  have hb : ∀ l, (b l : ℤ) = X.a l + k := fun l => Int.toNat_of_nonneg (le_trans (by positivity) (hnn l))
  obtain ⟨x, hxh, hxS⟩ := hd₀ b (fun l => by have h := hnn l; rw [← hb l] at h; exact_mod_cast h)
  obtain ⟨x', hx'h, hx'S⟩ := hd₀ (fun _ => k) (fun l => le_add_left (hle l))
  have hxs : IsSectionOn P (X.tensor HK) x :=
    ⟨b, fun l => by rw [hb l]; rfl, hxh, hxS P (Set.mem_insert _ _)⟩
  have hx's : IsSectionOn P HK x' := ⟨fun _ => k, fun _ => rfl, hx'h, hx'S P (Set.mem_insert _ _)⟩
  have hd : ∀ t : MRing ι, (∀ W ∈ S, t ∉ W) → ∀ W, W ∈ divSupp P y → W ∉ divSupp P t :=
    fun t ht W hW hWt =>
      ht W (Set.mem_insert_of_mem _ hW) (hWt.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self t)))
  have e1 := addX_sec I hR hRS hP hL hX hHK hY hy
  have e2 := swap_sec I hR hSwap hP hL (ThmIExists.smooth_tensor hX hHK) hY hxs hy (hd x hxS)
  have e3 := swap_sec I hR hSwap hP hL hHK hY hx's hy (hd x' hx'S)
  have e4 := hR.1 P (m + 1) (Fin.snoc L Y) X HK hP (smooth_snoc hL hY) hX hHK
  linarith

theorem swap_last (hR : IsRFamily I) (hRS : RPositionAdd.Statement) (hSwap : Swap.Statement)
    {P : Ideal (MRing ι)} {m : ℕ} (hP : IsArithVar P (m + 1 + 1)) {L : Fin m → HermLine ι}
    (hL : ∀ j, IsSmoothHerm (L j)) {X Y : HermLine ι} (hX : IsSmoothHerm X) (hY : IsSmoothHerm Y) :
    I P (m + 1 + 1) (Fin.snoc (Fin.snoc L X) Y) = I P (m + 1 + 1) (Fin.snoc (Fin.snoc L Y) X) := by
  set H : HermLine ι := ThmIExists.segreLine (ThmIExists.shift Y)
  have hH : IsSmoothHerm H := ThmIExists.isSmoothHerm_segreLine _
  have ht := ThmIExists.isSectionOn_up hP Y
  have hu := ThmIExists.isSectionOn_segre hP (ThmIExists.shift Y)
  have e1 := hR.1 P (m + 1) (Fin.snoc L X) Y H hP (smooth_snoc hL hX) hY hH
  have e2 := swap_half I hR hRS hSwap hP hL hX (ThmIExists.smooth_tensor hY hH) ht
  have e3 := swap_half I hR hRS hSwap hP hL hX hH hu
  have e4 := addX I hR hRS hP hL hY hH hX
  linarith

end Main

section Perm

omit [∀ k, Fintype (ι k)]

theorem snoc_comp_swap {n : ℕ} (L : Fin n → HermLine ι) (A : HermLine ι) (a b : Fin n) :
    (Fin.snoc L A : Fin (n + 1) → HermLine ι) ∘ Equiv.swap a.castSucc b.castSucc =
      Fin.snoc (L ∘ Equiv.swap a b) A := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne (Fin.castSucc_lt_last a).ne'
      (Fin.castSucc_lt_last b).ne']
    simp
  · have h : Equiv.swap a.castSucc b.castSucc j.castSucc = (Equiv.swap a b j).castSucc := by
      simp only [Equiv.swap_apply_def, Fin.castSucc_inj]
      split_ifs <;> rfl
    rw [Function.comp_apply, h]
    simp

theorem snoc_snoc_comp_swap {m : ℕ} (L : Fin m → HermLine ι) (X Y : HermLine ι) :
    (Fin.snoc (Fin.snoc L X) Y : Fin (m + 1 + 1) → HermLine ι) ∘
        Equiv.swap (Fin.last m).castSucc (Fin.last (m + 1)) =
      Fin.snoc (Fin.snoc L Y) X := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp
    · rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne
        (fun h => (Fin.castSucc_lt_last j).ne (Fin.castSucc_injective _ h))
        (Fin.castSucc_lt_last _).ne]
      simp

end Perm

end ThmISymm

theorem ThmISymm.proof (hSwap : Swap.Statement) (hRS : RPositionAdd.Statement) (hFC : FibreCompStatement)
    (hEU : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement (ZMod p) ι)
    (hSy : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ReciprocityTheory.ChartRestriction.G.AI.I1.SymmStatement (ZMod p) ι)
    (hGN : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ReciprocityTheory.ChartRestriction.G.AI.I1.GeoNumStatement ι) :
    ThmISymm.Statement := by
  intro K _ ι _ I hR
  suffices h : ∀ n P, IsArithVar P n → ∀ L : Fin n → HermLine ι, (∀ j, IsSmoothHerm (L j)) →
      ∀ σ : Equiv.Perm (Fin n), I P n (L ∘ σ) = I P n L from
    fun P n L σ hP hL => h n P hP L hL σ
  intro n
  induction n with
  | zero =>
    intro P _ L _ σ
    congr 1
    funext j
    exact j.elim0
  | succ n ih =>
    cases n with
    | zero =>
      intro P _ L _ σ
      congr 1
      funext j
      exact congrArg L (Fin.ext (by have := (σ j).isLt; have := j.isLt; omega))
    | succ m =>
      intro P hP
      suffices hc : ∀ σ ∈ Submonoid.closure
          (Set.range fun i : Fin (m + 1) => Equiv.swap i.castSucc i.succ),
          ∀ L : Fin (m + 1 + 1) → HermLine ι, (∀ j, IsSmoothHerm (L j)) →
            I P (m + 1 + 1) (L ∘ σ) = I P (m + 1 + 1) L by
        intro L hL σ
        refine hc σ ?_ L hL
        rw [Equiv.Perm.mclosure_swap_castSucc_succ]
        trivial
      intro σ hσ
      induction hσ using Submonoid.closure_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        intro L hL
        refine Fin.lastCases ?_ (fun i => ?_) i
        · have hdec : L = Fin.snoc (Fin.snoc (Fin.init (Fin.init L)) (Fin.init L (Fin.last m)))
              (L (Fin.last (m + 1))) := by simp [Fin.snoc_init_self]
          have hs : ∀ j, IsSmoothHerm (Fin.init (Fin.init L) j) := fun j => hL _
          dsimp only
          rw [Fin.succ_last, hdec, ThmISymm.snoc_snoc_comp_swap]
          exact (ThmISymm.swap_last I hR hRS hSwap hP hs (hL _) (hL _)).symm
        · have hdec : L = Fin.snoc (Fin.init L) (L (Fin.last (m + 1))) := by simp [Fin.snoc_init_self]
          have hs : ∀ j, IsSmoothHerm (Fin.init L j) := fun j => hL _
          dsimp only
          rw [Fin.succ_castSucc, hdec, ThmISymm.snoc_comp_swap]
          exact ThmISymm.lastFix I (fun p _ => hEU p K ι) (fun p _ => hSy p K ι) (hGN K ι) hFC hR hP ih
            (Fin.init L) hs _ (hL _) _
      | one =>
        intro L _
        rfl
      | mul x y _ _ hx hy =>
        intro L hL
        rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hy (L ∘ x) (fun j => hL (x j)), hx L hL]

end

end GroundTheory.Heights₂.Heights.Inter
