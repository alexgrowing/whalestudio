import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExistsAlgebraicClosureLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ComapLtOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.DifB
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.PtOfDif

noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4

namespace UpperTheory.V.Z.Kato.Sym

section

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} {X : Tower Ω ε} {m : ℕ}

end

private theorem ne_zero_of_pow_eq_io_of_ne_zero {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}
    {X : Tower Ω ε} {m : ℕ} (hm : 0 < m) {x : Kb X} {w : X.K} (hx : x ^ m = io X w) (hw : w ≠ 0) :
    x ≠ 0 := by
  rintro rfl
  rw [zero_pow hm.ne'] at hx
  exact hw ((map_eq_zero (io X)).mp hx.symm)

private theorem lg_prod_eq_sum_lg_of_pow_eq {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}
    {X : Tower Ω ε} {m : ℕ} (hm : 0 < m) {ι : Type} (S : Finset ι) (a b : ι → Kb X)
    (hb : ∀ k ∈ S, b k ≠ 0) (hab : ∀ k ∈ S, a k ^ m = b k ^ m) :
    lg X m (∏ k ∈ S, a k) (∏ k ∈ S, b k) = ∑ k ∈ S, lg X m (a k) (b k) := by
  classical
  obtain ⟨-, -, hlg2, -, hmul, -, -⟩ := lgB Ω ε X m hm
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact hlg2 1 1 0 one_ne_zero (by simp)
  | insert k S hk ih =>
    rw [Finset.prod_insert hk, Finset.prod_insert hk, Finset.sum_insert hk]
    have hb' : ∀ j ∈ S, b j ≠ 0 := fun j hj => hb j (Finset.mem_insert_of_mem hj)
    have hab' : ∀ j ∈ S, a j ^ m = b j ^ m := fun j hj => hab j (Finset.mem_insert_of_mem hj)
    rw [hmul _ _ _ _ (hb k (Finset.mem_insert_self k S)) (Finset.prod_ne_zero_iff.mpr hb')
      (hab k (Finset.mem_insert_self k S))
      (by rw [← Finset.prod_pow, ← Finset.prod_pow]; exact Finset.prod_congr rfl hab'), ih hb' hab']

private theorem ka_eq_of_pow_eq_io_eq {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}
    {X : Tower Ω ε} {m : ℕ} (hm : 0 < m) {h : RingAut (Kb X)} (hh : InD X h) {x y : Kb X} {w : X.K}
    (hx : x ^ m = io X w) (hy : y ^ m = io X w) (hw : w ≠ 0) : ka X m x h = ka X m y h := by
  obtain ⟨-, -, hlg2, hch, -, hσ, hcyc⟩ := lgB Ω ε X m hm
  obtain ⟨-, -, hrefl, -⟩ := admB Ω ε X
  have hx0 := ne_zero_of_pow_eq_io_of_ne_zero hm hx hw
  have hy0 := ne_zero_of_pow_eq_io_of_ne_zero hm hy hw
  have hfix : h (io X w) = io X w := hh w
  have hhx : (h x) ^ m = io X w := by rw [← map_pow, hx, hfix]
  have hhy : (h y) ^ m = io X w := by rw [← map_pow, hy, hfix]
  have hL : Lifts X h (RingEquiv.refl X.K) := fun f => hh f
  have e1 : lg X m (h x) (h y) = lg X m x y := by
    rw [hσ h _ 1 hrefl hL x y hy0 (hx.trans hy.symm), (hcyc 1 1).2.1, one_mul]
  have e2 : lg X m (h x) x = lg X m (h x) (h y) + lg X m (h y) x :=
    hch _ _ _ hx0 (hhx.trans hhy.symm) (hhy.trans hx.symm)
  have e3 : lg X m (h y) x = lg X m (h y) y + lg X m y x :=
    hch _ _ _ hx0 (hhy.trans hy.symm) (hy.trans hx.symm)
  have e4 : lg X m x x = lg X m x y + lg X m y x :=
    hch _ _ _ hx0 (hx.trans hy.symm) (hy.trans hx.symm)
  have e5 : lg X m x x = 0 := hlg2 x x 0 hx0 (by simp)
  unfold ka
  rw [e2, e3, e1]
  linear_combination e4.symm.trans e5

private theorem inD_conj_of_lifts {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}
    {X : Tower Ω ε} {τ : X.K ≃+* X.K} {σ h : RingAut (Kb X)} (hσL : Lifts X σ τ) (hh : InD X h) :
    InD X (σ⁻¹ * h * σ) := by
  unfold InD
  intro f
  have h1 : σ (io X f) = io X (τ f) := hσL f
  have h2 : h (io X (τ f)) = io X (τ f) := hh (τ f)
  have h3 : σ⁻¹ (io X (τ f)) = io X f := by rw [← h1]; simp
  rw [RingAut.mul_apply, RingAut.mul_apply, h1, h2, h3]
private theorem ka_apply_lift_eq_cyc_mul_ka_conj {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}
    {X : Tower Ω ε} {m : ℕ} (hm : 0 < m) {τ : X.K ≃+* X.K} {s : Gal(Ω/ℚ)} (hs : admitted X τ s)
    {σ h : RingAut (Kb X)} (hσL : Lifts X σ τ) (hh : InD X h) {x : Kb X} {w : X.K}
    (hx : x ^ m = io X w) (hw : w ≠ 0) :
    ka X m (σ x) h = cyc m s * ka X m x (σ⁻¹ * h * σ) := by
  obtain ⟨-, -, -, -, -, hσ, -⟩ := lgB Ω ε X m hm
  have hx0 := ne_zero_of_pow_eq_io_of_ne_zero hm hx hw
  unfold ka
  have e : σ ((σ⁻¹ * h * σ) x) = h (σ x) := by simp [RingAut.mul_apply]
  rw [← e]
  refine hσ σ τ s hs hσL _ _ hx0 ?_
  have h1 : σ (io X w) = io X (τ w) := hσL w
  have h2 : h (io X (τ w)) = io X (τ w) := hh (τ w)
  have h3 : σ⁻¹ (io X (τ w)) = io X w := by rw [← h1]; simp
  rw [← map_pow, hx, RingAut.mul_apply, RingAut.mul_apply, h1, h2, h3]

private theorem dif_mv_eq_of_dif_eq_zero {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}
    {X : Tower Ω ε} {m : ℕ} (hm : 0 < m) {τ : X.K ≃+* X.K} {s : Gal(Ω/ℚ)} (hs : admitted X τ s)
    {σ h : RingAut (Kb X)} (hσL : Lifts X σ τ) (hh : InD X h) {u v : X.K} (hu : u ≠ 0) (hv : v ≠ 0)
    (P Q P' Q' : Pt X m) (hPa : P.a ^ m = io X u) (hQa : Q.a ^ m = io X u)
    (hPb : P.b ^ m = io X v) (hQb : Q.b ^ m = io X v)
    (hP'a : P'.a ^ m = io X (τ u)) (hQ'a : Q'.a ^ m = io X (τ u))
    (hP'b : P'.b ^ m = io X (τ v)) (hQ'b : Q'.b ^ m = io X (τ v))
    (hPQ : ∀ k, InD X k → dif X P Q k = 0) (hPQ' : dif X P' Q' h = 0) :
    dif X (Pt.mv σ (cyc m s) P) P' h = dif X (Pt.mv σ (cyc m s) Q) Q' h := by
  obtain ⟨-, -, -, hch, -, hσ, -⟩ := lgB Ω ε X m hm
  have hτu : τ u ≠ 0 := (map_ne_zero τ).mpr hu
  have hτv : τ v ≠ 0 := (map_ne_zero τ).mpr hv
  have hgD := inD_conj_of_lifts hσL hh
  have E1 := hPQ _ hgD
  have hσPa : (σ P.a) ^ m = io X (τ u) := by rw [← map_pow, hPa]; exact hσL u
  have hσQa : (σ Q.a) ^ m = io X (τ u) := by rw [← map_pow, hQa]; exact hσL u
  have hσPb : (σ P.b) ^ m = io X (τ v) := by rw [← map_pow, hPb]; exact hσL v
  have hσQb : (σ Q.b) ^ m = io X (τ v) := by rw [← map_pow, hQb]; exact hσL v
  have kA1 : ka X m Q.a (σ⁻¹ * h * σ) = ka X m P.a (σ⁻¹ * h * σ) := ka_eq_of_pow_eq_io_eq hm hgD hQa hPa hu
  have kB1 : ka X m Q.b (σ⁻¹ * h * σ) = ka X m P.b (σ⁻¹ * h * σ) := ka_eq_of_pow_eq_io_eq hm hgD hQb hPb hv
  have kA2 : cyc m s * ka X m P.a (σ⁻¹ * h * σ) = ka X m P'.a h := by
    rw [← ka_apply_lift_eq_cyc_mul_ka_conj hm hs hσL hh hPa hu]; exact ka_eq_of_pow_eq_io_eq hm hh hσPa hP'a hτu
  have kB2 : cyc m s * ka X m P.b (σ⁻¹ * h * σ) = ka X m P'.b h := by
    rw [← ka_apply_lift_eq_cyc_mul_ka_conj hm hs hσL hh hPb hv]; exact ka_eq_of_pow_eq_io_eq hm hh hσPb hP'b hτv
  have kA3 : ka X m Q'.a h = ka X m P'.a h := ka_eq_of_pow_eq_io_eq hm hh hQ'a hP'a hτu
  have kB3 : ka X m Q'.b h = ka X m P'.b h := ka_eq_of_pow_eq_io_eq hm hh hQ'b hP'b hτv
  have hQa0 := ne_zero_of_pow_eq_io_of_ne_zero hm hQa hu
  have hQb0 := ne_zero_of_pow_eq_io_of_ne_zero hm hQb hv
  have hQ'a0 := ne_zero_of_pow_eq_io_of_ne_zero hm hQ'a hτu
  have hQ'b0 := ne_zero_of_pow_eq_io_of_ne_zero hm hQ'b hτv
  have la : lg X m (σ P.a) (σ Q.a) = cyc m s * lg X m P.a Q.a :=
    hσ σ τ s hs hσL _ _ hQa0 (hPa.trans hQa.symm)
  have lb : lg X m (σ P.b) (σ Q.b) = cyc m s * lg X m P.b Q.b :=
    hσ σ τ s hs hσL _ _ hQb0 (hPb.trans hQb.symm)
  have Ca : lg X m (σ P.a) Q'.a = lg X m (σ P.a) (σ Q.a) + lg X m (σ Q.a) Q'.a :=
    hch _ _ _ hQ'a0 (hσPa.trans hσQa.symm) (hσQa.trans hQ'a.symm)
  have Ca' : lg X m (σ P.a) Q'.a = lg X m (σ P.a) P'.a + lg X m P'.a Q'.a :=
    hch _ _ _ hQ'a0 (hσPa.trans hP'a.symm) (hP'a.trans hQ'a.symm)
  have Cb : lg X m (σ P.b) Q'.b = lg X m (σ P.b) (σ Q.b) + lg X m (σ Q.b) Q'.b :=
    hch _ _ _ hQ'b0 (hσPb.trans hσQb.symm) (hσQb.trans hQ'b.symm)
  have Cb' : lg X m (σ P.b) Q'.b = lg X m (σ P.b) P'.b + lg X m P'.b Q'.b :=
    hch _ _ _ hQ'b0 (hσPb.trans hP'b.symm) (hP'b.trans hQ'b.symm)
  unfold dif at E1 hPQ' ⊢
  unfold Pt.mv
  dsimp only
  rw [kA1, kB1] at E1
  rw [kA3, kB3] at hPQ' ⊢
  linear_combination (cyc m s) ^ 2 * E1 - hPQ' + ka X m P'.a h * (Cb - Cb')
    - ka X m P'.b h * (Ca - Ca') - (cyc m s * lg X m P.b Q.b) * kA2 + ka X m P'.a h * lb
    - (cyc m s * ka X m P.b (σ⁻¹ * h * σ)) * la + lg X m (σ P.a) (σ Q.a) * kB2
private theorem dif_mv_independent_of_lift {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}
    {X : Tower Ω ε} {m : ℕ} (hm : 0 < m) {τ : X.K ≃+* X.K} {s : Gal(Ω/ℚ)} (hs : admitted X τ s)
    {σ σ' h : RingAut (Kb X)} (h1 : Lifts X σ τ) (h2 : Lifts X σ' τ) {u v : X.K} {P P' : Pt X m}
    (hP : IsPt X m u v P) (hP' : IsPt X m (τ u) (τ v) P') (hh : InD X h) :
    dif X (Pt.mv σ (cyc m s) P) P' h = dif X (Pt.mv σ' (cyc m s) P) P' h := by
  obtain ⟨-, -, hrefl, -⟩ := admB Ω ε X
  obtain ⟨-, -, -, -, -, -, hcyc⟩ := lgB Ω ε X m hm
  have hδL : Lifts X (σ'⁻¹ * σ) (RingEquiv.refl X.K) := by
    unfold Lifts
    intro f
    have a1 : σ (io X f) = io X (τ f) := h1 f
    have a2 : σ' (io X f) = io X (τ f) := h2 f
    rw [RingAut.mul_apply, a1, ← a2]
    simp
  have hδD : InD X (σ'⁻¹ * σ) := fun f => hδL f
  have hY := mvPt Ω ε X m hm _ _ hrefl (σ'⁻¹ * σ) hδL u v P hP
  rw [(hcyc 1 1).2.1] at hY
  have hmv : Pt.mv σ (cyc m s) P = Pt.mv σ' (cyc m s) (Pt.mv (σ'⁻¹ * σ) 1 P) := by
    unfold Pt.mv
    simp [RingAut.mul_apply, mul_assoc]
  have hA := mvPt Ω ε X m hm τ s hs σ h1 u v P hP
  have hB := mvPt Ω ε X m hm τ s hs σ' h2 u v P hP
  obtain ⟨-, -, -, htri, -, -, -⟩ := difB Ω ε X m hm _ _ _ _ hA hB
  obtain ⟨-, -, -, -, -, -, h7⟩ := difB Ω ε X m hm _ _ _ _ hY hP
  obtain ⟨-, -, -, -, -, h6, -⟩ := difB Ω ε X m hm _ _ _ _ hP hP
  have z : dif X (Pt.mv σ (cyc m s) P) (Pt.mv σ' (cyc m s) P) h = 0 := by
    rw [hmv, h7 τ s hs σ' h2 h hh, h6 _ hδD _ (inD_conj_of_lifts h2 hh), mul_zero]
  rw [htri P' hP' h hh, z, zero_add]

theorem sumMv : SumMv := by
  intro Ω _ _ _ ε X m hm I J A A' B B' u u' v v' P P' R R' e e' τ s hs hA hB he he' hP hP' hu hv hR hR' f hf
  classical
  obtain ⟨-, -, -, -, -, -, hlift, -⟩ := admB Ω ε X
  obtain ⟨σ, hσL⟩ := hlift τ
  unfold IsSum at hR hR'
  obtain ⟨α, β, η, hQ, rfl⟩ := hR
  obtain ⟨α', β', η', hQ', rfl⟩ := hR'
  obtain ⟨i0, hi0⟩ := hA
  obtain ⟨j0, hj0⟩ := hB
  obtain ⟨i1, hi1, -⟩ := he.surjOn hi0
  obtain ⟨j1, hj1, -⟩ := he'.surjOn hj0
  have hPt : ∀ i ∈ A, ∀ j ∈ B, (P i j).a ^ m = io X (u i) ∧ (P i j).b ^ m = io X (v j) ∧
      u i ≠ 0 ∧ v j ≠ 0 := by
    intro i hi j hj
    obtain ⟨h1, h2, ha, hb, -⟩ := hP i hi j hj
    exact ⟨ha, hb, h1.1, h2.1⟩
  have hPt' : ∀ i ∈ A', ∀ j ∈ B', (P' i j).a ^ m = io X (u' i) ∧ (P' i j).b ^ m = io X (v' j) ∧
      u' i ≠ 0 ∧ v' j ≠ 0 := by
    intro i hi j hj
    obtain ⟨h1, h2, ha, hb, -⟩ := hP' i hi j hj
    exact ⟨ha, hb, h1.1, h2.1⟩
  have hα : ∀ i ∈ A, α i ^ m = io X (u i) := fun i hi => (hQ i hi j0 hj0).1.trans (hPt i hi j0 hj0).1
  have hβ : ∀ j ∈ B, β j ^ m = io X (v j) := fun j hj => (hQ i0 hi0 j hj).2.1.trans (hPt i0 hi0 j hj).2.1
  have hα' : ∀ i ∈ A', α' i ^ m = io X (u' i) := fun i hi =>
    (hQ' i hi j1 hj1).1.trans (hPt' i hi j1 hj1).1
  have hβ' : ∀ j ∈ B', β' j ^ m = io X (v' j) := fun j hj =>
    (hQ' i1 hi1 j hj).2.1.trans (hPt' i1 hi1 j hj).2.1
  have hu0 : ∀ i ∈ A, u i ≠ 0 := fun i hi => (hPt i hi j0 hj0).2.2.1
  have hv0 : ∀ j ∈ B, v j ≠ 0 := fun j hj => (hPt i0 hi0 j hj).2.2.2
  have hu0' : ∀ i ∈ A', u' i ≠ 0 := fun i hi => (hPt' i hi j1 hj1).2.2.1
  have hv0' : ∀ j ∈ B', v' j ≠ 0 := fun j hj => (hPt' i1 hi1 j hj).2.2.2
  have hk : ∀ i ∈ A', ∀ j ∈ B', ∃ θ : Kb X, θ ^ m = io X (f i j) ∧ ∀ h, InD X h →
      ka X m θ h = dif X (Pt.mv σ (cyc m s) (Pt.mk (α (e i)) (β (e' j)) (η (e i) (e' j))))
        (Pt.mk (α' i) (β' j) (η' i j)) h := by
    intro i hi j hj
    have hei : e i ∈ A := he.mapsTo hi
    have hej : e' j ∈ B := he'.mapsTo hj
    obtain ⟨σ', hσ', θ, hθ, hθk⟩ := hf i hi j hj
    refine ⟨θ, hθ, fun h hh => ?_⟩
    have hPij := hP (e i) hei (e' j) hej
    have hP'ij := hP' i hi j hj
    rw [hu i hi, hv j hj] at hP'ij
    rw [hθk h hh, ← dif_mv_independent_of_lift hm hs hσL hσ' hPij hP'ij hh]
    exact dif_mv_eq_of_dif_eq_zero hm hs hσL hh (hPt _ hei _ hej).2.2.1 (hPt _ hei _ hej).2.2.2 _ _ _ _
      (hPt _ hei _ hej).1 (hα _ hei) (hPt _ hei _ hej).2.1 (hβ _ hej)
      (by rw [← hu i hi]; exact (hPt' i hi j hj).1) (by rw [← hu i hi]; exact hα' i hi)
      (by rw [← hv j hj]; exact (hPt' i hi j hj).2.1) (by rw [← hv j hj]; exact hβ' j hj)
      (fun k hk => (hQ _ hei _ hej).2.2 k hk) ((hQ' i hi j hj).2.2 h hh)
  choose! θ hθ hθk using hk
  unfold Mv IsKum
  refine ⟨σ, hσL, ∏ i ∈ A', ∏ j ∈ B', θ i j, ?_, ?_⟩
  · calc (∏ i ∈ A', ∏ j ∈ B', θ i j) ^ m = ∏ i ∈ A', ∏ j ∈ B', io X ↑(f i j) := by
          rw [← Finset.prod_pow]
          refine Finset.prod_congr rfl fun i hi => ?_
          rw [← Finset.prod_pow]
          exact Finset.prod_congr rfl fun j hj => hθ i hi j hj
      _ = io X ↑(∏ i ∈ A', ∏ j ∈ B', f i j) := by simp only [Units.coe_prod, map_prod]
  · intro h hh
    have hD : InD X h := hh
    have hθ0 : ∀ i ∈ A', ∀ j ∈ B', θ i j ≠ 0 := fun i hi j hj =>
      ne_zero_of_pow_eq_io_of_ne_zero hm (hθ i hi j hj) (f i j).ne_zero
    have L : ka X m (∏ i ∈ A', ∏ j ∈ B', θ i j) h = ∑ i ∈ A', ∑ j ∈ B', ka X m (θ i j) h := by
      unfold ka
      simp only [map_prod]
      rw [← Finset.prod_product', ← Finset.prod_product', ← Finset.sum_product']
      refine lg_prod_eq_sum_lg_of_pow_eq hm _ _ _ (fun x hx => ?_) (fun x hx => ?_)
      · rw [Finset.mem_product] at hx
        exact hθ0 _ hx.1 _ hx.2
      · rw [Finset.mem_product] at hx
        rw [← map_pow, hθ _ hx.1 _ hx.2]
        exact hD _
    rw [L, Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => hθk i hi j hj h hD]
    have F1 : ∑ i ∈ A', ∑ j ∈ B', η (e i) (e' j) (σ⁻¹ * h * σ) = ∑ i ∈ A, ∑ j ∈ B, η i j (σ⁻¹ * h * σ) := by
      refine Finset.sum_nbij e (fun a ha => he.mapsTo ha) he.injOn he.surjOn fun i hi => ?_
      exact Finset.sum_nbij e' (fun a ha => he'.mapsTo ha) he'.injOn he'.surjOn fun j hj => rfl
    have F2 : ka X m (∏ i ∈ A', α' i) h = ∑ i ∈ A', ka X m (α' i) h := by
      unfold ka
      rw [map_prod]
      refine lg_prod_eq_sum_lg_of_pow_eq hm _ _ _ (fun i hi => ne_zero_of_pow_eq_io_of_ne_zero hm (hα' i hi) (hu0' i hi)) (fun i hi => ?_)
      rw [← map_pow, hα' i hi]
      exact hD _
    have F3 : ka X m (∏ j ∈ B', β' j) h = ∑ j ∈ B', ka X m (β' j) h := by
      unfold ka
      rw [map_prod]
      refine lg_prod_eq_sum_lg_of_pow_eq hm _ _ _ (fun j hj => ne_zero_of_pow_eq_io_of_ne_zero hm (hβ' j hj) (hv0' j hj)) (fun j hj => ?_)
      rw [← map_pow, hβ' j hj]
      exact hD _
    have F4 : lg X m (σ (∏ j ∈ B, β j)) (∏ j ∈ B', β' j) = ∑ j ∈ B', lg X m (σ (β (e' j))) (β' j) := by
      have r : ∏ j ∈ B, σ (β j) = ∏ j ∈ B', σ (β (e' j)) :=
        (Finset.prod_nbij e' (fun a ha => he'.mapsTo ha) he'.injOn he'.surjOn fun j hj => rfl).symm
      rw [map_prod, r]
      refine lg_prod_eq_sum_lg_of_pow_eq hm _ _ _ (fun j hj => ne_zero_of_pow_eq_io_of_ne_zero hm (hβ' j hj) (hv0' j hj)) (fun j hj => ?_)
      rw [← map_pow, hβ _ (he'.mapsTo hj), hβ' j hj, hv j hj]
      exact hσL _
    have F5 : lg X m (σ (∏ i ∈ A, α i)) (∏ i ∈ A', α' i) = ∑ i ∈ A', lg X m (σ (α (e i))) (α' i) := by
      have r : ∏ i ∈ A, σ (α i) = ∏ i ∈ A', σ (α (e i)) :=
        (Finset.prod_nbij e (fun a ha => he.mapsTo ha) he.injOn he.surjOn fun i hi => rfl).symm
      rw [map_prod, r]
      refine lg_prod_eq_sum_lg_of_pow_eq hm _ _ _ (fun i hi => ne_zero_of_pow_eq_io_of_ne_zero hm (hα' i hi) (hu0' i hi)) (fun i hi => ?_)
      rw [← map_pow, hα _ (he.mapsTo hi), hα' i hi, hu i hi]
      exact hσL _
    unfold dif Pt.mv
    dsimp only
    rw [← F1, F2, F3, F4, F5, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.mul_sum]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]

end UpperTheory.V.Z.Kato.Sym

end
