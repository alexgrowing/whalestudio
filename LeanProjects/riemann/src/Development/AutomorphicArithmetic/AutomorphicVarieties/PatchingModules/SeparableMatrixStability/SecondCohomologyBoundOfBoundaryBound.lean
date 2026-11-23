import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SelmerSecondExistsUltrafilterLimit
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SelRed

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem power_series_exists_ultrafilter_limit {K : Type} [Field K] [Finite K] (U : Ultrafilter ℕ) (c : ℕ → PowerSeries K) :
    ∃ c0 : PowerSeries K, ∀ j, ∀ᶠ m in (U : Filter ℕ), (PowerSeries.X : PowerSeries K) ^ j ∣ c m - c0 := by
  have hv : ∀ i : ℕ, ∃ v : K, {m | PowerSeries.coeff i (c m) = v} ∈ (U : Filter ℕ) := by
    intro i
    by_contra hno
    push_neg at hno
    have hall : ∀ v : K, {m | PowerSeries.coeff i (c m) = v}ᶜ ∈ U := fun v =>
      Ultrafilter.compl_mem_iff_notMem.2 (hno v)
    have hinter : (⋂ v : K, {m | PowerSeries.coeff i (c m) = v}ᶜ) ∈ (U : Filter ℕ) :=
      Filter.iInter_mem.2 hall
    obtain ⟨m, hm⟩ := Filter.nonempty_of_mem hinter
    simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_setOf_eq] at hm
    exact hm _ rfl
  choose v hv using hv
  refine ⟨PowerSeries.mk v, fun j => ?_⟩
  have hj : ∀ᶠ m in (U : Filter ℕ), ∀ i : Fin j, PowerSeries.coeff (i : ℕ) (c m) = v i :=
    Filter.eventually_all.2 fun i => hv i
  filter_upwards [hj] with m hm
  rw [PowerSeries.X_pow_dvd_iff]
  intro i hi
  simp [map_sub, hm ⟨i, hi⟩, PowerSeries.coeff_mk]

private theorem power_series_eq_of_dvd_all_powers {K : Type} [Field K] (a b : PowerSeries K)
    (H : ∀ j, (PowerSeries.X : PowerSeries K) ^ j ∣ a - b) : a = b := by
  rw [← sub_eq_zero]
  ext n
  have h := H (n + 1)
  rw [PowerSeries.X_pow_dvd_iff] at h
  simpa using h n (Nat.lt_succ_self n)

private theorem dual_numbers_map_surjective {A X X' : Type} [CommRing A] [CommRing X] [CommRing X'] [Algebra A X] [Algebra A X'] (g : ℕ)
    (f : X →ₐ[A] X') (hf : Function.Surjective f) : Function.Surjective (DD.map g f) := by
  intro y
  choose pre hpre using hf
  exact ⟨⟨pre y.a, fun j => pre (y.ep j), fun j => pre (y.ep' j), pre y.eta⟩,
    DD.ext (hpre _) (funext fun j => hpre _) (funext fun j => hpre _) (hpre _)⟩

theorem UpperTheory.V.Pa.secondCohomologyBound_of_boundaryBound :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x), TopFG G.Γ → SecondSelmerSpanBoundAtAllLevels h k → K2 h k := by
  intro l _ L G G0 h n x k hTop hB2 z hz
  obtain ⟨C, hC⟩ := hB2
  set q : ∀ m : ℕ, x.A →ₐ[x.A] x.Am m := fun m => Ideal.Quotient.mkₐ x.A (Ideal.span {x.t ^ m}) with hqdef
  have hsurj : ∀ m, Function.Surjective (q m) := fun m => Ideal.Quotient.mkₐ_surjective _ _
  have hqeq : ∀ m (u v : x.A), q m u = q m v ↔ (PowerSeries.X : PowerSeries x.K) ^ m ∣ u - v := by
    intro m u v
    simp only [hqdef, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq, Ideal.mem_span_singleton] <;> rfl
  have hzm : ∀ m i j, (fun g => (z i j g).map (q m)) ∈ SelP h x (x.Am m) :=
    fun m i j => (sel_red l L G G0 h n x k x.A (x.Am m) (q m)).1 _ (hz i j)
  choose cm hcu Ψm hΨm hΨe using fun m => hC m (fun i j g => (z i j g).map (q m)) (hzm m)
  choose Ψt hΨt using fun m (g : G.G₀) (a b : Fin n) =>
    dual_numbers_map_surjective k.g (q m) (hsurj m) (Ψm m g a b)
  set Z : ℕ → G.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g) :=
    fun m g => Matrix.of (fun a b => Ψt m g a b) with hZdef
  have hZ : ∀ m, (fun g => (Z m g).map (x.redD k.g m)) = Ψm m := by
    intro m
    funext g
    exact Matrix.ext fun a b => hΨt m g a b
  set U := Ultrafilter.of (atTop : Filter ℕ) with hUdef
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨Ψ, hΨ, hlim⟩ := selmer_second_exists_ultrafilter_limit l L G G0 h n x k U Z hTop hU (fun m => by rw [hZ m]; exact hΨm m)
  choose c0 hc0 using fun i : Fin (k.g + 1) => power_series_exists_ultrafilter_limit U (fun m => cm m i)
  choose idx hidx using hcu
  have hi0 : ∃ i0, ∀ᶠ m in (U : Filter ℕ), idx m = i0 := by
    by_contra hno
    push_neg at hno
    have hinter : ∀ᶠ m in (U : Filter ℕ), ∀ i, ¬ idx m = i :=
      Filter.eventually_all.2 fun i => by simpa using hno i
    obtain ⟨m, hm⟩ := hinter.exists
    exact hm _ rfl
  obtain ⟨i0, hi0⟩ := hi0
  refine ⟨fun i => x.t ^ C * c0 i, ?_, Ψ, hΨ, ?_⟩
  · intro h0
    have h1 : x.t ^ C * c0 i0 = 0 := congrFun h0 i0
    have hc00 : c0 i0 = 0 := by
      rcases mul_eq_zero.1 h1 with h2 | h2
      · exact absurd h2 (pow_ne_zero _ PowerSeries.X_ne_zero)
      · exact h2
    obtain ⟨m, hm1, hm2⟩ := (hi0.and (hc0 i0 1)).exists
    have hu := hidx m
    rw [hm1] at hu
    have h3 : (PowerSeries.X : PowerSeries x.K) ∣ cm m i0 := by
      simpa [hc00] using hm2
    have h7 := isUnit_of_dvd_unit h3 hu
    simp [PowerSeries.isUnit_iff_constantCoeff] at h7
  · intro j γ a b
    apply power_series_eq_of_dvd_all_powers
    intro J
    obtain ⟨m, hm1, hm2, hm3⟩ := ((hlim J).and ((Filter.eventually_all.2 fun i => hc0 i J).and
      ((Filter.eventually_ge_atTop J).filter_mono hU))).exists
    have d1 : (PowerSeries.X : PowerSeries x.K) ^ J ∣ (Ψ γ a b).ep' j - (Ψt m γ a b).ep' j := by
      have e := congrArg (fun M => (M a b).ep' j) (hm1 γ)
      exact (hqeq J ((Ψ γ a b).ep' j) ((Ψt m γ a b).ep' j)).1 e
    have d2 : (PowerSeries.X : PowerSeries x.K) ^ J ∣
        (Ψt m γ a b).ep' j - x.t ^ C * ∑ i, cm m i * z i j γ a b := by
      have e := hΨe m j γ a b
      rw [← hΨt m γ a b] at e
      have e2 : q m ((Ψt m γ a b).ep' j) = q m (x.t ^ C * ∑ i, cm m i * z i j γ a b) := by
        rw [show q m ((Ψt m γ a b).ep' j) = (DD.map k.g (q m) (Ψt m γ a b)).ep' j from rfl, e]
        simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.map_apply]
        rw [map_mul, map_sum]
        simp only [map_mul]
        rw [Algebra.smul_def, ← (q m).commutes, Algebra.algebraMap_self, RingHom.id_apply]
        congr 1
      exact (pow_dvd_pow _ hm3).trans ((hqeq m _ _).1 e2)
    have d3 : (PowerSeries.X : PowerSeries x.K) ^ J ∣
        x.t ^ C * ∑ i, cm m i * z i j γ a b - (∑ i, (x.t ^ C * c0 i) • z i j γ) a b := by
      have e : x.t ^ C * ∑ i, cm m i * z i j γ a b - (∑ i, (x.t ^ C * c0 i) • z i j γ) a b =
          x.t ^ C * ∑ i, (cm m i - c0 i) * z i j γ a b := by
        simp [Matrix.sum_apply, Finset.mul_sum, ← Finset.sum_sub_distrib, sub_mul, mul_sub, mul_assoc]
      rw [e]
      exact Dvd.dvd.mul_left (Finset.dvd_sum fun i _ => Dvd.dvd.mul_right (hm2 i) _) _
    have := dvd_add (dvd_add d1 d2) d3
    simpa using this
