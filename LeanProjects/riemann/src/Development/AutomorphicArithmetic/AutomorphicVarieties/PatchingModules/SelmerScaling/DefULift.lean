import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.LocLemma
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.InverseWeylLiftEqPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.OddDiag
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.HomBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.BndRho
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.BndOps

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

section SlopeTestRemainingChoices
variable {X : Type} [CommRing X] {g n : ℕ}

private theorem sub_a (x y : DD X g) : (x - y).a = x.a - y.a := by simp [sub_eq_add_neg]
private theorem sub_ep (x y : DD X g) (j) : (x - y).ep j = x.ep j - y.ep j := by simp [sub_eq_add_neg]
private theorem sub_ep' (x y : DD X g) (j) : (x - y).ep' j = x.ep' j - y.ep' j := by simp [sub_eq_add_neg]

private theorem sum_cmp {ι : Type} (s : Finset ι) (f : ι → DD X g) :
    (∑ i ∈ s, f i).a = ∑ i ∈ s, (f i).a ∧ (∀ j, (∑ i ∈ s, f i).ep j = ∑ i ∈ s, (f i).ep j) ∧
      (∀ j, (∑ i ∈ s, f i).ep' j = ∑ i ∈ s, (f i).ep' j) ∧ (∑ i ∈ s, f i).eta = ∑ i ∈ s, (f i).eta := by
  refine ⟨map_sum (AddMonoidHom.mk' DD.a DD.add_a) f s, fun j => ?_, fun j => ?_,
    map_sum (AddMonoidHom.mk' DD.eta DD.add_eta) f s⟩
  · exact map_sum (AddMonoidHom.mk' (fun x : DD X g => x.ep j) (fun x y => DD.add_ep x y j)) f s
  · exact map_sum (AddMonoidHom.mk' (fun x : DD X g => x.ep' j) (fun x y => DD.add_ep' x y j)) f s

private def II (X : Type) [CommRing X] (g : ℕ) : Ideal (DD X g) where
  carrier := {x | x.a = 0 ∧ ∀ j, x.ep j = 0}
  add_mem' := by rintro x y ⟨a, b⟩ ⟨c, d⟩; exact ⟨by simp [a, c], fun j => by simp [b, d]⟩
  zero_mem' := ⟨rfl, fun _ => rfl⟩
  smul_mem' := by rintro c x ⟨a, b⟩; exact ⟨by simp [a], fun j => by simp [a, b]⟩

private theorem II_mul {x y : DD X g} (hx : x ∈ II X g) (hy : y ∈ II X g) : x * y = 0 := by
  obtain ⟨xa, xe⟩ := hx
  obtain ⟨ya, ye⟩ := hy
  apply DD.ext
  · simp [DD.mul_a, xa]
  · funext j; simp [DD.mul_ep, xa, ya]
  · funext j; simp [DD.mul_ep', xa, ya]
  · simp [DD.mul_eta, xa, ya, xe, ye]

private theorem II_mat {M N : Matrix (Fin n) (Fin n) (DD X g)} (hx : ∀ i j, M i j ∈ II X g)
    (hy : ∀ i j, N i j ∈ II X g) : M * N = 0 := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply, Matrix.zero_apply]
  exact Finset.sum_eq_zero fun c _ => II_mul (hx _ _) (hy _ _)

private theorem II_right {M : Matrix (Fin n) (Fin n) (DD X g)} (N : Matrix (Fin n) (Fin n) (DD X g))
    (hx : ∀ i j, M i j ∈ II X g) (i j) : (M * N) i j ∈ II X g := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_right _ _ (hx _ _)

private theorem aug_nil (x : DD X g) (hx : x.a = 0) : IsNilpotent x := by
  refine ⟨3, ?_⟩
  have e2 : (x * x).a = 0 ∧ ∀ j, (x * x).ep j = 0 := ⟨by simp [DD.mul_a, hx], fun j => by simp [DD.mul_ep, hx]⟩
  have e3 : x ^ 3 = x * (x * x) := by ring
  rw [e3]
  apply DD.ext
  · simp [DD.mul_a, hx]
  · funext j; simp [DD.mul_ep, hx, e2.1]
  · funext j; simp [DD.mul_ep', hx, e2.1]
  · simp [DD.mul_eta, hx, e2.1, e2.2]

private def P0 (x : DD X g) : Prop := (∀ j, x.ep j = 0) ∧ x.eta = 0
private def P1 (x : DD X g) : Prop := x.a = 0 ∧ ∀ j, x.ep' j = 0

private theorem zeroth_part_sum {ι : Type} (s : Finset ι) (f : ι → DD X g) (h : ∀ i, P0 (f i)) : P0 (∑ i ∈ s, f i) := by
  obtain ⟨-, he, -, ht⟩ := sum_cmp s f
  refine ⟨fun j => ?_, ?_⟩
  · rw [he j]
    exact Finset.sum_eq_zero fun i _ => (h i).1 j
  · rw [ht]
    exact Finset.sum_eq_zero fun i _ => (h i).2

private theorem first_part_sum {ι : Type} (s : Finset ι) (f : ι → DD X g) (h : ∀ i, P1 (f i)) : P1 (∑ i ∈ s, f i) := by
  obtain ⟨ha, -, he, -⟩ := sum_cmp s f
  refine ⟨?_, fun j => ?_⟩
  · rw [ha]
    exact Finset.sum_eq_zero fun i _ => (h i).1
  · rw [he j]
    exact Finset.sum_eq_zero fun i _ => (h i).2 j

private theorem product_zeroth_terms {x y : DD X g} (hx : P0 x) (hy : P0 y) : P0 (x * y) := by
  obtain ⟨xe, xt⟩ := hx
  obtain ⟨ye, yt⟩ := hy
  exact ⟨fun j => by simp [DD.mul_ep, xe, ye], by simp [DD.mul_eta, xe, ye, xt, yt]⟩
private theorem product_first_partition {x y : DD X g} (hx : P1 x) (hy : P1 y) : P0 (x * y) := by
  obtain ⟨xa, xe⟩ := hx
  obtain ⟨ya, ye⟩ := hy
  exact ⟨fun j => by simp [DD.mul_ep, xa, ya], by simp [DD.mul_eta, xa, ya, xe, ye]⟩
private theorem product_zeroth_first_parts {x y : DD X g} (hx : P0 x) (hy : P1 y) : P1 (x * y) := by
  obtain ⟨xe, xt⟩ := hx
  obtain ⟨ya, ye⟩ := hy
  exact ⟨by simp [DD.mul_a, ya], fun j => by simp [DD.mul_ep', ya, ye]⟩
private theorem product_first_zeroth_parts {x y : DD X g} (hx : P1 x) (hy : P0 y) : P1 (x * y) := by
  obtain ⟨xa, xe⟩ := hx
  obtain ⟨ye, yt⟩ := hy
  exact ⟨by simp [DD.mul_a, xa], fun j => by simp [DD.mul_ep', xa, xe]⟩

private def EE (X : Type) [CommRing X] (g n a : ℕ) : Subalgebra X (Matrix (Fin n) (Fin n) (DD X g)) where
  carrier := {Z | ∀ i j : Fin n, ((((i : ℕ) < a) ↔ ((j : ℕ) < a)) → P0 (Z i j)) ∧
    (¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → P1 (Z i j))}
  mul_mem' := by
    intro M N hM hN i j
    rw [Matrix.mul_apply]
    refine ⟨fun e => zeroth_part_sum _ _ fun c => ?_, fun e => first_part_sum _ _ fun c => ?_⟩
    · by_cases e' : ((i : ℕ) < a) ↔ ((c : ℕ) < a)
      · exact product_zeroth_terms ((hM i c).1 e') ((hN c j).1 (by tauto))
      · exact product_first_partition ((hM i c).2 e') ((hN c j).2 (by tauto))
    · by_cases e' : ((i : ℕ) < a) ↔ ((c : ℕ) < a)
      · exact product_zeroth_first_parts ((hM i c).1 e') ((hN c j).2 (by tauto))
      · exact product_first_zeroth_parts ((hM i c).2 e') ((hN c j).1 (by tauto))
  add_mem' := by
    intro M N hM hN i j
    refine ⟨fun e => ?_, fun e => ?_⟩
    · obtain ⟨a1, a2⟩ := (hM i j).1 e
      obtain ⟨b1, b2⟩ := (hN i j).1 e
      exact ⟨fun k => by simp [a1, b1], by simp [a2, b2]⟩
    · obtain ⟨a1, a2⟩ := (hM i j).2 e
      obtain ⟨b1, b2⟩ := (hN i j).2 e
      exact ⟨by simp [a1, b1], fun k => by simp [a2, b2]⟩
  algebraMap_mem' := by
    intro c i j
    rw [Matrix.algebraMap_matrix_apply]
    refine ⟨fun e => ?_, fun e => ?_⟩
    · split_ifs
      · exact ⟨fun _ => rfl, rfl⟩
      · exact ⟨fun _ => rfl, rfl⟩
    · rw [if_neg (by rintro rfl; exact e Iff.rfl)]
      exact ⟨rfl, fun _ => rfl⟩

private theorem EE_scal {a : ℕ} {c : DD X g} (hc : P0 c) :
    algebraMap (DD X g) (Matrix (Fin n) (Fin n) (DD X g)) c ∈ EE X g n a := by
  intro i j
  rw [Matrix.algebraMap_matrix_apply]
  refine ⟨fun e => ?_, fun e => ?_⟩
  · split_ifs
    · exact hc
    · exact ⟨fun _ => rfl, rfl⟩
  · rw [if_neg (by rintro rfl; exact e Iff.rfl)]
    exact ⟨rfl, fun _ => rfl⟩

variable {A : Type} [CommRing A] [Algebra A X] {a : ℕ}

private theorem EE_of_even {M : Matrix (Fin n) (Fin n) (DD X g)}
    (h : M ∈ blkMat n a (ddPart A X g true false true false) (ddPart A X g false true false true)) : M ∈ EE X g n a := by
  intro i j
  obtain ⟨h1, h2⟩ := h i j
  refine ⟨fun e => ?_, fun e => ?_⟩
  · obtain ⟨-, he, -, ht⟩ := h1 e
    exact ⟨fun k => congrFun (he rfl) k, ht rfl⟩
  · obtain ⟨ha, -, he, -⟩ := h2 e
    exact ⟨ha rfl, fun k => congrFun (he rfl) k⟩

private theorem mem_even_entries_of_first_order {M : Matrix (Fin n) (Fin n) (DD X g)} (h : M ∈ W1 n A X g a) : M ∈ EE X g n a := by
  intro i j
  obtain ⟨h1, h2⟩ := h i j
  refine ⟨fun e => ?_, fun e => ?_⟩
  · obtain ⟨-, he, -, ht⟩ := h1 e
    exact ⟨fun k => congrFun (he rfl) k, ht rfl⟩
  · obtain ⟨ha, -, he, -⟩ := h2 e
    exact ⟨ha rfl, fun k => congrFun (he rfl) k⟩

private theorem mem_second_order_of_reductions {M : Matrix (Fin n) (Fin n) (DD X g)} (h : M ∈ EE X g n a) (h' : ∀ i j, M i j ∈ II X g) :
    M ∈ W2 n A X g a := by
  intro i j
  obtain ⟨h1, h2⟩ := h i j
  obtain ⟨ia, ie⟩ := h' i j
  refine ⟨fun e => ?_, fun e => ?_⟩
  · obtain ⟨pe, pt⟩ := h1 e
    exact ⟨fun _ => ia, fun _ => funext pe, nofun, fun _ => pt⟩
  · obtain ⟨pa, pe⟩ := h2 e
    exact ⟨fun _ => pa, fun _ => funext ie, fun _ => funext pe, nofun⟩

end SlopeTestRemainingChoices

private theorem first_order_lift_apply {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type) [CommRing X]
    [Algebra x.A X] (γ : F.G₀) (a b : Fin n) :
    k.ρ1 X γ a b = ⟨x.ρX X γ a b, fun j => ((k.κ j γ).map (algebraMap x.A X) * x.ρX X γ) a b, 0, 0⟩ := by
  have hC : ∀ c d, x.ρX (DD X k.g) γ c d = ⟨x.ρX X γ c d, 0, 0, 0⟩ := fun _ _ => rfl
  obtain ⟨s1, s2, s3, s4⟩ := sum_cmp Finset.univ fun c =>
    DD.epM (fun j => (k.κ j γ).map (algebraMap x.A X)) a c * x.ρX (DD X k.g) γ c b
  have e : k.ρ1 X γ a b = x.ρX (DD X k.g) γ a b +
      ∑ c, DD.epM (fun j => (k.κ j γ).map (algebraMap x.A X)) a c * x.ρX (DD X k.g) γ c b := by
    rw [Kap.ρ1, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply]
  rw [e]
  apply DD.ext
  · rw [DD.add_a, s1]
    simp [hC, DD.epM, DD.mul_a]
  · funext j
    rw [DD.add_ep, s2]
    simp [hC, DD.epM, DD.mul_ep, Matrix.mul_apply]
  · funext j
    rw [DD.add_ep', s3]
    simp [hC, DD.epM, DD.mul_ep']
  · rw [DD.add_eta, s4]
    simp [hC, DD.epM, DD.mul_eta]

private theorem dd_eta_sub {X : Type} [CommRing X] {g : ℕ} (x y : DD X g) : (x - y).eta = x.eta - y.eta := by
  simp [sub_eq_add_neg]

private theorem bnd_mul {K G : Type} [Field K] [TopologicalSpace G] [Group G] [IsTopologicalGroup G] {n e : ℕ}
    {u r : G → Matrix (Fin n) (Fin n) (DD (FractionRing (PowerSeries K)) e)}
    (hu : BndD (PowerSeries.X : PowerSeries K) u) (hr : BndD (PowerSeries.X : PowerSeries K) r) :
    BndD (PowerSeries.X : PowerSeries K) fun g => u g * r g - 1 := by
  obtain ⟨hc, hop, hsum, -, -⟩ := bndOps K G
  have add : ∀ φ ψ : G → FractionRing (PowerSeries K), BndF (PowerSeries.X : PowerSeries K) φ →
      BndF (PowerSeries.X : PowerSeries K) ψ → BndF (PowerSeries.X : PowerSeries K) (fun g => φ g + ψ g) :=
    fun φ ψ a b => (hop φ ψ a b).1
  have mul : ∀ φ ψ : G → FractionRing (PowerSeries K), BndF (PowerSeries.X : PowerSeries K) φ →
      BndF (PowerSeries.X : PowerSeries K) ψ → BndF (PowerSeries.X : PowerSeries K) (fun g => φ g * ψ g) :=
    fun φ ψ a b => (hop φ ψ a b).2.1
  have sub : ∀ φ ψ : G → FractionRing (PowerSeries K), BndF (PowerSeries.X : PowerSeries K) φ →
      BndF (PowerSeries.X : PowerSeries K) ψ → BndF (PowerSeries.X : PowerSeries K) (fun g => φ g - ψ g) := by
    intro φ ψ a b
    simp only [sub_eq_add_neg]
    exact add _ _ a (hop ψ ψ b b).2.2.1
  have sm : ∀ {ι : Type} (s : Finset ι) (φ : ι → G → FractionRing (PowerSeries K)),
      (∀ i, BndF (PowerSeries.X : PowerSeries K) (φ i)) →
      BndF (PowerSeries.X : PowerSeries K) (fun g => ∑ i ∈ s, φ i g) :=
    fun s φ h => hsum _ s φ fun i _ => h i
  have sa : ∀ f : Fin n → DD (FractionRing (PowerSeries K)) e, (∑ c, f c).a = ∑ c, (f c).a :=
    fun f => (sum_cmp _ f).1
  have se : ∀ (f : Fin n → DD (FractionRing (PowerSeries K)) e) q, (∑ c, f c).ep q = ∑ c, (f c).ep q :=
    fun f => (sum_cmp _ f).2.1
  have se' : ∀ (f : Fin n → DD (FractionRing (PowerSeries K)) e) q, (∑ c, f c).ep' q = ∑ c, (f c).ep' q :=
    fun f => (sum_cmp _ f).2.2.1
  have st : ∀ f : Fin n → DD (FractionRing (PowerSeries K)) e, (∑ c, f c).eta = ∑ c, (f c).eta :=
    fun f => (sum_cmp _ f).2.2.2
  intro i j
  refine ⟨?_, fun q => ?_, fun q => ?_, ?_⟩
  · simp only [Matrix.sub_apply, Matrix.mul_apply, sub_a, sa, DD.mul_a]
    refine sub _ _ (sm _ _ fun c => mul _ _ (hu i c).1 (hr c j).1) (hc _)
  · simp only [Matrix.sub_apply, Matrix.mul_apply, sub_ep, se, DD.mul_ep]
    refine sub _ _ (sm _ _ fun c => add _ _ (mul _ _ (hu i c).1 ((hr c j).2.1 q))
      (mul _ _ ((hu i c).2.1 q) (hr c j).1)) (hc _)
  · simp only [Matrix.sub_apply, Matrix.mul_apply, sub_ep', se', DD.mul_ep']
    refine sub _ _ (sm _ _ fun c => add _ _ (mul _ _ (hu i c).1 ((hr c j).2.2.1 q))
      (mul _ _ ((hu i c).2.2.1 q) (hr c j).1)) (hc _)
  · simp only [Matrix.sub_apply, Matrix.mul_apply, dd_eta_sub, st, DD.mul_eta]
    refine sub _ _ (sm _ _ fun c => add _ _ (add _ _ (mul _ _ (hu i c).1 (hr c j).2.2.2)
      (mul _ _ (hu i c).2.2.2 (hr c j).1)) (sm _ _ fun q => add _ _
        (mul _ _ ((hu i c).2.1 q) ((hr c j).2.2.1 q)) (mul _ _ ((hu i c).2.2.1 q) ((hr c j).2.1 q)))) (hc _)

theorem UpperTheory.V.Pa.defULift :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), ∀ (u : G.G₀ → Matrix (Fin n) (Fin n) (DD x.Fr k.g)) (ψ : ∀ v, Fin n → L.Gv v →* (DD x.Fr k.g)ˣ), DefU h x u ψ → (∀ j, epC h x u j = kapF h k j) → Lifts h k (epC' h x u) := by
  intro l _ L G G0 h n x k u ψ hU hE
  obtain ⟨Tmul, Tone, Tform, Tine, TW1, Tloc⟩ := rho1Tri l L G G0 h n x k x.Fr
  obtain ⟨-, -, Bconj, Bφ, BIu, Beps⟩ := homBasic l L G G0 h
  have rinv : ∀ γ : G.G₀, k.ρ1 x.Fr (h.p₀ γ) * k.ρ1 x.Fr (h.p₀ γ⁻¹) = 1 := by
    intro γ
    rw [← Tmul, ← map_mul, mul_inv_cancel, map_one, Tone]
  have rinv' : ∀ γ : G.G₀, k.ρ1 x.Fr (h.p₀ γ⁻¹) * k.ρ1 x.Fr (h.p₀ γ) = 1 := by
    intro γ
    rw [← Tmul, ← map_mul, inv_mul_cancel, map_one, Tone]
  have uinv : ∀ γ : G.G₀, u γ * u γ⁻¹ = 1 := by
    intro γ
    rw [← hU.mul, mul_inv_cancel, hU.one]
  have ρXh : ∀ g, x.ρX x.Fr g = ((algebraMap x.A x.Fr).mapMatrix.toMonoidHom.comp (mat x.ρ)) g :=
    fun _ => rfl
  have ρXinv : ∀ g : G0.G₀, x.ρX x.Fr g⁻¹ * x.ρX x.Fr g = 1 := by
    intro g
    rw [ρXh, ρXh, ← map_mul, inv_mul_cancel, map_one]
  have hep : ∀ γ q, (u γ).map (fun a => a.ep q) =
      (k.κ q (h.p₀ γ)).map (algebraMap x.A x.Fr) * x.ρX x.Fr (h.p₀ γ) := by
    intro γ q
    have e := congrFun (hE q) γ
    simp only [epC, kapF] at e
    rw [← e, mul_assoc, map_inv, ρXinv, mul_one]
  have hD : ∀ γ i j, (u γ - k.ρ1 x.Fr (h.p₀ γ)) i j ∈ II x.Fr k.g := by
    intro γ i j
    refine ⟨?_, fun q => ?_⟩
    · have e := congrFun (congrFun (hU.red γ) i) j
      simp only [Matrix.map_apply] at e
      rw [Matrix.sub_apply, sub_a, first_order_lift_apply]
      simp [e]
    · have e := congrFun (congrFun (hep γ q) i) j
      simp only [Matrix.map_apply] at e
      rw [Matrix.sub_apply, sub_ep, first_order_lift_apply]
      simp [e]
  have hZe : ∀ γ : G.G₀, u γ * k.ρ1 x.Fr (h.p₀ γ⁻¹) - 1 =
      (u γ - k.ρ1 x.Fr (h.p₀ γ)) * k.ρ1 x.Fr (h.p₀ γ⁻¹) := by
    intro γ
    rw [sub_mul, rinv]
  have hZ : ∀ γ : G.G₀, ∀ i j, (u γ * k.ρ1 x.Fr (h.p₀ γ⁻¹) - 1) i j ∈ II x.Fr k.g := by
    intro γ
    rw [hZe]
    exact II_right _ (hD γ)
  have hsq : ∀ γ : G.G₀, (u γ * k.ρ1 x.Fr (h.p₀ γ⁻¹) - 1) * (u γ * k.ρ1 x.Fr (h.p₀ γ⁻¹) - 1) = 0 :=
    fun γ => II_mat (hZ γ) (hZ γ)
  refine ⟨fun γ => u γ * k.ρ1 x.Fr (h.p₀ γ⁻¹) - 1, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro γ
    exact mem_second_order_of_reductions (Subalgebra.sub_mem _ (Subalgebra.mul_mem _ (EE_of_even (hU.even γ)) (mem_even_entries_of_first_order (TW1 _)))
      (Subalgebra.one_mem _)) (hZ γ)
  · intro i j
    have ht : IsUnit (algebraMap x.A (DD x.Fr k.g) x.t) := by
      have e : algebraMap x.A (DD x.Fr k.g) x.t = DD.C (algebraMap x.A x.Fr x.t) := rfl
      rw [e]
      exact (IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective x.A x.Fr)).mpr
        PowerSeries.X_ne_zero)).map DD.C
    rw [Ideal.span_singleton_eq_top.mpr ht]
    intro N
    exact IsLocallyConstant.of_constant _ fun _ _ => Ideal.Quotient.eq.mpr (by rw [Ideal.top_pow]; exact Submodule.mem_top)
  · intro g g'
    dsimp only
    rw [hU.mul, _root_.mul_inv_rev, map_mul, Tmul]
    have key := II_mat (hD g) (hZ g')
    rw [← sub_eq_zero]
    have e : u g * u g' * (k.ρ1 x.Fr (h.p₀ g'⁻¹) * k.ρ1 x.Fr (h.p₀ g⁻¹)) - 1 -
        (u g * k.ρ1 x.Fr (h.p₀ g⁻¹) - 1 + k.ρ1 x.Fr (h.p₀ g) * (u g' * k.ρ1 x.Fr (h.p₀ g'⁻¹) - 1) *
          k.ρ1 x.Fr (h.p₀ g⁻¹)) =
        (u g - k.ρ1 x.Fr (h.p₀ g)) * (u g' * k.ρ1 x.Fr (h.p₀ g'⁻¹) - 1) * k.ρ1 x.Fr (h.p₀ g⁻¹) := by
      noncomm_ring
    rw [e, key, zero_mul]
  · intro g
    dsimp only
    have hf1 := hU.form g
    have hf2 := Tform (h.p₀ g)
    rw [← Bconj g, Beps ℤ_[l] x.A g] at hf2
    have e1 : u (G.frame.conj g) = (u g⁻¹)ᵀ * ((u g)ᵀ * u (G.frame.conj g)) := by
      rw [← mul_assoc, ← Matrix.transpose_mul, uinv, Matrix.transpose_one, one_mul]
    have e2 : (u g)ᵀ * u (G.frame.conj g) * k.ρ1 x.Fr (h.p₀ (G.frame.conj g)⁻¹) =
        (k.ρ1 x.Fr (h.p₀ g))ᵀ := by
      rw [hf1, ← hf2, mul_assoc, rinv, mul_one]
    have e4 : (1 - (u g * k.ρ1 x.Fr (h.p₀ g⁻¹) - 1)) * (1 + (u g * k.ρ1 x.Fr (h.p₀ g⁻¹) - 1)) = 1 := by
      rw [show (1 - (u g * k.ρ1 x.Fr (h.p₀ g⁻¹) - 1)) * (1 + (u g * k.ρ1 x.Fr (h.p₀ g⁻¹) - 1)) =
        1 - (u g * k.ρ1 x.Fr (h.p₀ g⁻¹) - 1) * (u g * k.ρ1 x.Fr (h.p₀ g⁻¹) - 1) by noncomm_ring, hsq, sub_zero]
    have e3 : k.ρ1 x.Fr (h.p₀ g) * u g⁻¹ = 1 - (u g * k.ρ1 x.Fr (h.p₀ g⁻¹) - 1) := by
      calc k.ρ1 x.Fr (h.p₀ g) * u g⁻¹
          = (1 - (u g * k.ρ1 x.Fr (h.p₀ g⁻¹) - 1)) * (1 + (u g * k.ρ1 x.Fr (h.p₀ g⁻¹) - 1)) *
              (k.ρ1 x.Fr (h.p₀ g) * u g⁻¹) := by rw [e4, one_mul]
        _ = (1 - (u g * k.ρ1 x.Fr (h.p₀ g⁻¹) - 1)) *
              (u g * (k.ρ1 x.Fr (h.p₀ g⁻¹) * k.ρ1 x.Fr (h.p₀ g)) * u g⁻¹) := by
            rw [add_sub_cancel]
            simp only [mul_assoc]
        _ = 1 - (u g * k.ρ1 x.Fr (h.p₀ g⁻¹) - 1) := by rw [rinv', mul_one, uinv, mul_one]
    rw [e1, mul_assoc, e2, ← Matrix.transpose_mul, e3, Matrix.transpose_sub, Matrix.transpose_one]
    abel
  · intro w g hg
    dsimp only
    rw [Tine w _ (BIu w _ (inv_mem hg)), hU.ine w g hg, mul_one, sub_self]
  · intro v
    haveI : Infinite x.Fr := by
      have hA : Infinite x.A := by
        refine Infinite.of_injective (fun m : ℕ => (PowerSeries.X : PowerSeries x.K) ^ m) fun m m' e => ?_
        have e' := congrArg (PowerSeries.coeff m) e
        simp only [PowerSeries.coeff_X_pow, if_true] at e'
        by_contra hne
        rw [if_neg hne] at e'
        exact one_ne_zero e'
      exact Infinite.of_injective _ (IsFractionRing.injective x.A x.Fr)
    obtain ⟨w1w, ww1, tri⟩ := Tloc v
    let ρ₀ : L.Gv v →* Matrix (Fin n) (Fin n) (DD x.Fr k.g) :=
      { toFun := fun g => k.ρ1 x.Fr (h.p₀ (G.φ v g))
        map_one' := by simp [Tone]
        map_mul' := by
          intro a b
          simp [Tmul] }
    let ρ₁ : L.Gv v →* Matrix (Fin n) (Fin n) (DD x.Fr k.g) :=
      { toFun := fun g => u (G.φ v g)
        map_one' := by simp [hU.one]
        map_mul' := by
          intro a b
          simp [hU.mul] }
    let ψ₀ : Fin n → L.Gv v →* DD x.Fr k.g := fun i =>
      (algebraMap x.A (DD x.Fr k.g)).toMonoidHom.comp ((Units.coeHom x.A).comp (x.ψ v i))
    let ψ₁ : Fin n → L.Gv v →* DD x.Fr k.g := fun i => (Units.coeHom _).comp (ψ v i)
    have hnil : ∀ a, DD.aug x.Fr k.g a = 0 → IsNilpotent a := fun a ha => aug_nil a ha
    have hsqI : II x.Fr k.g * II x.Fr k.g = ⊥ := by
      rw [eq_bot_iff, Ideal.mul_le]
      intro a ha b hb
      rw [II_mul ha hb]
      exact Submodule.zero_mem _
    have htri : ∀ g, (∀ i j, j < i → (k.wi1 x.Fr v * ρ₀ g * k.w1 x.Fr v) i j = 0) ∧
        ∀ i, (k.wi1 x.Fr v * ρ₀ g * k.w1 x.Fr v) i i = ψ₀ i g := by
      intro g
      have e : ρ₀ g = k.ρ1 x.Fr ((G0.φ v) g) := by
        show k.ρ1 x.Fr (h.p₀ (G.φ v g)) = _
        rw [Bφ]
      rw [e]
      exact tri g
    have hd1 : ∀ g i j, ρ₁ g i j - ρ₀ g i j ∈ II x.Fr k.g := fun g i j => by
      have e := hD (G.φ v g) i j
      rwa [Matrix.sub_apply] at e
    have hd2 : ∀ i g, ψ₁ i g - ψ₀ i g ∈ II x.Fr k.g := by
      intro i g
      refine ⟨?_, fun q => ?_⟩
      · rw [sub_a]
        exact sub_eq_zero.mpr (hU.ψ_red v i g)
      · rw [sub_ep]
        exact sub_eq_zero.mpr (congrFun ((hU.ψ_even v i g).2.1 rfl) q)
    have hdist : ∀ i j, i ≠ j → ∃ g, DD.aug x.Fr k.g (ψ₀ i g) ≠ DD.aug x.Fr k.g (ψ₀ j g) := by
      intro i j hij
      obtain ⟨g, hg⟩ := DFunLike.ne_iff.mp ((x.N1 v).1 i j hij)
      exact ⟨g, fun e => hg (Units.ext (IsFractionRing.injective x.A x.Fr e))⟩
    have hE1 : ∀ g, ρ₀ g ∈ EE x.Fr k.g n x.a ∧ ρ₁ g ∈ EE x.Fr k.g n x.a :=
      fun g => ⟨mem_even_entries_of_first_order (TW1 _), EE_of_even (hU.even _)⟩
    have hE2 : ∀ i g, algebraMap (DD x.Fr k.g) (Matrix (Fin n) (Fin n) (DD x.Fr k.g)) (ψ₀ i g) ∈ EE x.Fr k.g n x.a ∧
        algebraMap (DD x.Fr k.g) (Matrix (Fin n) (Fin n) (DD x.Fr k.g)) (ψ₁ i g) ∈ EE x.Fr k.g n x.a :=
      fun i g => ⟨EE_scal ⟨fun _ => rfl, rfl⟩,
        EE_scal ⟨congrFun ((hU.ψ_even v i g).2.1 rfl), (hU.ψ_even v i g).2.2.2 rfl⟩⟩
    obtain ⟨Y, hYE, hYI, hY⟩ := locLemma x.Fr (DD x.Fr k.g) (L.Gv v) n (DD.aug x.Fr k.g) (II x.Fr k.g)
      (EE x.Fr k.g n x.a) ρ₀ ρ₁ ψ₀ ψ₁ (k.w1 x.Fr v) (k.wi1 x.Fr v) hnil hsqI w1w ww1 htri hd1 hd2 hdist
      (fun g => hU.ord v g) hE1 hE2
    refine ⟨Y, mem_second_order_of_reductions hYE hYI, fun g => ⟨fun i j hij => ?_, fun hg i => ?_⟩⟩
    · have hρ₀inv : ρ₀ g⁻¹ = k.ρ1 x.Fr (h.p₀ ((G.φ v g)⁻¹)) := by
        show k.ρ1 x.Fr (h.p₀ (G.φ v g⁻¹)) = _
        rw [map_inv (G.φ v)]
      have e := (hY g).1 i j hij
      rw [hρ₀inv] at e
      exact e
    · have hρ₀inv : ρ₀ g⁻¹ = k.ρ1 x.Fr (h.p₀ ((G.φ v g)⁻¹)) := by
        show k.ρ1 x.Fr (h.p₀ (G.φ v g⁻¹)) = _
        rw [map_inv (G.φ v)]
      have h0 : ψ₀ i g = 1 := by
        show algebraMap x.A (DD x.Fr k.g) ↑(x.ψ v i g) = 1
        rw [x.ψ_mu v i g hg]
        simp
      have h1 : ψ₁ i g = 1 := by
        show ((ψ v i g : (DD x.Fr k.g)ˣ) : DD x.Fr k.g) = 1
        rw [hU.ψ_mu v i g hg]
        rfl
      have e := (hY g).2 i
      rw [hρ₀inv, h0, h1, mul_one, sub_self] at e
      exact e
  · obtain ⟨hc, hop, hsum, -, -⟩ := bndOps x.K G.G₀
    obtain ⟨-, bρi, bκ⟩ := bndRho l L G G0 h n x k
    refine bnd_mul hU.bnd fun i j => ?_
    simp only [first_order_lift_apply]
    refine ⟨bρi i j, fun q => ?_, fun q => hc 0, hc 0⟩
    simp only [Matrix.mul_apply]
    exact hsum _ _ _ fun c _ => (hop _ _ ((hop _ _ (bκ q i c) (bκ q i c)).2.2.2) (bρi c j)).2.1
  · intro j γ a b
    dsimp only
    have h1 : ((1 : Matrix (Fin n) (Fin n) (DD x.Fr k.g)) a b).ep' j = 0 := by
      rw [Matrix.one_apply]
      split_ifs <;> simp
    rw [Matrix.sub_apply, sub_ep', h1, sub_zero, Matrix.mul_apply, (sum_cmp _ _).2.2.1]
    simp only [epC', Matrix.mul_apply, Matrix.map_apply, DD.mul_ep', first_order_lift_apply]
    clear Tmul Tone Tform Tine TW1 Tloc Bconj Bφ BIu Beps rinv rinv' uinv ρXh ρXinv hep hD hZe hZ hsq
    simp
