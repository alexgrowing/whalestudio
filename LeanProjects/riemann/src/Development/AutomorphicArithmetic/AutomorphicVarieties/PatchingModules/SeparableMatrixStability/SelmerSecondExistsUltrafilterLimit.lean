import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SelmerSecondClosedUnderLimits
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SelRed
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.CocFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.RhoHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.AmFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UltraFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SubgroupQuot
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem diag_mk {K : Type} [Field K] (a : ℕ → PowerSeries K) (b : PowerSeries K) (j : ℕ)
    (H : ∀ c < j, Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries K) ^ (c + 1)}) b =
      Ideal.Quotient.mk _ (a c)) :
    Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries K) ^ j})
      (PowerSeries.mk fun c => PowerSeries.coeff c (a c)) = Ideal.Quotient.mk _ b := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
  intro c hc
  have := H c hc
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at this
  have := this c (Nat.lt_succ_self c)
  rw [map_sub, sub_eq_zero] at this ⊢
  rw [PowerSeries.coeff_mk, this]

private theorem lc_of_nil {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (t : R) (ht : IsNilpotent t) (f : Γ → R)
    (hf : AdicCont (Ideal.span {t}) f) : IsLocallyConstant f := by
  obtain ⟨N, hN⟩ := ht
  have h1 : IsLocallyConstant fun g => Ideal.Quotient.mk (Ideal.span {t} ^ N) (f g) := hf N
  refine IsLocallyConstant.desc f (Ideal.Quotient.mk (Ideal.span {t} ^ N)) h1 ?_
  rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, Ideal.span_singleton_pow, hN, Ideal.span_singleton_eq_bot]

private theorem lc_mat {Γ R : Type} [TopologicalSpace Γ] {n : ℕ} (f : Γ → Matrix (Fin n) (Fin n) R)
    (hf : ∀ i j, IsLocallyConstant fun g => f g i j) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  have : ∀ᶠ g in nhds y, ∀ i j, f g i j = f y i j :=
    eventually_all.2 fun i => eventually_all.2 fun j => (hf i j).eventually_eq y
  exact this.mono fun g hg => Matrix.ext hg

private theorem selmer_second_finite_modulo_power (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n)
    (k : Kap x) (hG : TopFG G.Γ) (j : ℕ) : (Sel2 h (x.Am j) k).Finite := by
  obtain ⟨hfin, -, hn, hn', -⟩ := am_fin l G0.frame n x j k.g
  obtain ⟨-, ⟨h1, hm, -⟩, hlc, -⟩ := rho_hom l G0.frame n x k (x.Am j)
  have hfg : TopFG G.G₀ := (TopFG.subgroup_quot G.Γ hG).1 G.η.ker G.η_open
  have := coc_fin G.G₀ (DD (x.Am j) k.g) n (fun g => k.ρ1 (x.Am j) (h.p₀ g)) hfg
    (by simp only [map_one]; exact h1) (fun g g' => by simp only [map_mul]; exact hm _ _)
    ((hlc hn).2.comp_continuous h.p₀_cont)
  refine this.subset ?_
  rintro z ⟨-, h2, h3, -⟩
  exact ⟨lc_mat z fun a b => lc_of_nil _ hn' _ (h2 a b), h3⟩

theorem UpperTheory.V.Pa.selmer_second_exists_ultrafilter_limit :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (U : Ultrafilter ℕ) (z : ℕ → G.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g)), TopFG G.Γ → (U : Filter ℕ) ≤ atTop → (∀ m, (fun g => (z m g).map (x.redD k.g m)) ∈ Sel2 h (x.Am m) k) → ∃ Ψ ∈ Sel2 h x.A k, ∀ j, ∀ᶠ m in (U : Filter ℕ), ∀ g, (Ψ g).map (x.redD k.g j) = (z m g).map (x.redD k.g j) := by
  intro l _ L G G0 h n x k U z hG hU hz
  have hred : ∀ j, ∀ᶠ m in (U : Filter ℕ), (fun g => (z m g).map (x.redD k.g j)) ∈ Sel2 h (x.Am j) k := by
    intro j
    refine ((eventually_ge_atTop j).filter_mono hU).mono fun m hm => ?_
    have hle : Ideal.span {x.t ^ m} ≤ Ideal.span {x.t ^ j} :=
      Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ hm)
    exact (sel_red l L G G0 h n x k (x.Am m) (x.Am j) (Ideal.Quotient.factorₐ x.A hle)).2.2.1 _ (hz m)
  have hst : ∀ j, ∃ m', ∀ᶠ m in (U : Filter ℕ),
      (fun g => (z m g).map (x.redD k.g j)) = fun g => (z m' g).map (x.redD k.g j) := by
    intro j
    obtain ⟨w, ⟨-, hw⟩, -⟩ := ultra_fin ℕ _ U (fun m g => (z m g).map (x.redD k.g j)) _
      (selmer_second_finite_modulo_power l L G G0 h n x k hG j) (hred j)
    obtain ⟨m', hm'⟩ := hw.exists
    exact ⟨m', hw.mono fun m hm => hm.trans hm'.symm⟩
  choose μ hμ using hst
  let Ψ : G.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g) := fun g => Matrix.of fun a b =>
    ⟨PowerSeries.mk fun c => PowerSeries.coeff c (z (μ (c + 1)) g a b).a,
     fun i => PowerSeries.mk fun c => PowerSeries.coeff c ((z (μ (c + 1)) g a b).ep i),
     fun i => PowerSeries.mk fun c => PowerSeries.coeff c ((z (μ (c + 1)) g a b).ep' i),
     PowerSeries.mk fun c => PowerSeries.coeff c (z (μ (c + 1)) g a b).eta⟩
  have hΨ : ∀ j, ∀ᶠ m in (U : Filter ℕ), ∀ g, (Ψ g).map (x.redD k.g j) = (z m g).map (x.redD k.g j) := by
    intro j
    have h1 : ∀ᶠ m in (U : Filter ℕ), ∀ c ∈ Finset.range j,
        (fun g => (z m g).map (x.redD k.g (c + 1))) = fun g => (z (μ (c + 1)) g).map (x.redD k.g (c + 1)) :=
      (Filter.eventually_all_finset _).2 fun c _ => hμ (c + 1)
    refine h1.mono fun m hm g => Matrix.ext fun a b => ?_
    have h2 : ∀ c < j, x.redD k.g (c + 1) (z m g a b) = x.redD k.g (c + 1) (z (μ (c + 1)) g a b) := fun c hc =>
      congrFun (congrFun (congrFun (hm c (Finset.mem_range.2 hc)) g) a) b
    refine DD.ext ?_ (funext fun i => ?_) (funext fun i => ?_) ?_
    · exact diag_mk (fun c => (z (μ (c + 1)) g a b).a) _ j fun c hc => congrArg DD.a (h2 c hc)
    · exact diag_mk (fun c => (z (μ (c + 1)) g a b).ep i) _ j fun c hc => congrArg (DD.ep · i) (h2 c hc)
    · exact diag_mk (fun c => (z (μ (c + 1)) g a b).ep' i) _ j fun c hc => congrArg (DD.ep' · i) (h2 c hc)
    · exact diag_mk (fun c => (z (μ (c + 1)) g a b).eta) _ j fun c hc => congrArg DD.eta (h2 c hc)
  refine ⟨Ψ, selmer_second_closed_under_limits l L G G0 h n x k Ψ fun j => ?_, hΨ⟩
  obtain ⟨m, hm1, hm2⟩ := ((hΨ j).and (hred j)).exists
  rw [funext hm1]
  exact hm2
