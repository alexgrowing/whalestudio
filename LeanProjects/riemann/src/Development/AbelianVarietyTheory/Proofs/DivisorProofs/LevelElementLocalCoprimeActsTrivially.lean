import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

namespace GlobalTheory.FrameTriv

theorem map_eq_one_of_isLocEnv {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {Pl0 : Type} (pl : Pl0 → HeightOneSpectrum (𝓞 D.host.E)) (ok : Set Pl0)
    (i : ok × ℕ) (x : Bridge.Gf V) (hloc : isLocEnv V pl ok i x) (l : ℕ) (hl : (l : 𝓞 D.host.E) ∉ (pl i.1).asIdeal)
    {R : Type} [CommRing R] (ev : (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* R)
    (hev : ∀ a : FiniteAdeleRing (𝓞 D.host.F) D.host.F,
      (∀ v : HeightOneSpectrum (𝓞 D.host.F), (l : 𝓞 D.host.F) ∈ v.asIdeal → a v = 0) → ev (a ⊗ₜ[D.host.F] 1) = 0) :
    (x.1.val : Matrix (Fin V.rank) (Fin V.rank) ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E)).map ev = 1 := by
  obtain ⟨e, α, he, -, hS, hx⟩ := hloc
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨-, ε, hε, hf⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ (Or.inl ⟨he, rfl⟩)
  obtain ⟨εf, hεf, -, h0⟩ := hε
  have hvan : ev (εf ⊗ₜ[D.host.F] (1 : D.host.E)) = 0 := by
    refine hev εf fun v' hv' => h0 v' ?_
    rintro rfl
    apply hl
    have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (l : 𝓞 D.host.F) ∈ (pl i.1).asIdeal := hv'
    rwa [map_natCast] at h2
  let φ : Formalism.L2.Theta.AE D →+* (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E :=
    (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hmat : ∀ a c, x.1.val a c = φ ((Formalism.L2.Theta.mt V α) a c) := by
    intro a c
    rw [hx]
    rfl
  have hφε : φ (algebraMap _ (Formalism.L2.Theta.AE D) ε) = εf ⊗ₜ[D.host.F] (1 : D.host.E) := by
    rw [hεf]
    rfl
  let ψ : Formalism.L2.Theta.AE D →+* R := ev.comp φ
  have hψ : ψ (algebraMap _ (Formalism.L2.Theta.AE D) ε) = 0 := (congrArg ev hφε).trans hvan
  ext a c
  have hsplit : Formalism.L2.Theta.mt V α a c =
      algebraMap _ (Formalism.L2.Theta.AE D) ε * (Formalism.L2.Theta.mt V α - 1) a c + (1 : Matrix _ _ (Formalism.L2.Theta.AE D)) a c := by
    rw [← hf, hS a c, Matrix.sub_apply, sub_add_cancel]
  refine (congrArg ev (hmat a c)).trans ?_
  show ψ _ = _
  rw [hsplit, ψ.map_add, ψ.map_mul, hψ, zero_mul, zero_add, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact ψ.map_one
  · exact ψ.map_zero

theorem intEmb_injective {l : ℕ} [Fact l.Prime] (Lf : IntermediateField ℚ_[l] (PadicAlgCl l)) : Function.Injective (intEmb Lf) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

theorem kap_eq_one {O K : Type} [CommRing O] [CommRing K] {f : O →+* K} (hf : Function.Injective f) {N n : ℕ} (g : GL (Fin N) O)
    (b : GL (Fin N) K) (M : Matrix (Fin n) (Fin n) K) (rk : Fin N → Fin n) (hrk : Function.Injective rk) (hM : M = 1)
    (h : (Matrix.GeneralLinearGroup.map f g).val = (b⁻¹).val * M.submatrix rk rk * b.val) : g = 1 := by
  rw [hM, Matrix.submatrix_one _ hrk, mul_one, Units.inv_mul] at h
  refine Units.ext (Matrix.ext fun a c => hf ?_)
  have h3 : f (g.val a c) = (1 : Matrix (Fin N) (Fin N) K) a c := congrFun (congrFun h a) c
  rw [h3, Units.val_one, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact f.map_one.symm
  · exact f.map_zero.symm

theorem chi_eq_one {O K ι : Type} [CommRing O] [Field K] [Fintype ι] {f : O →+* K} (hf : Function.Injective f) {N : ℕ}
    (io : K ≃+* ℂ) (g : ι → GL (Fin N) O) (sh : ι → ℤ) (x : Oˣ) (y : ℂˣ) (hg : g = 1) (hy : y = 1)
    (h : io (f x * ∏ τ, f (g τ).val.det ^ sh τ) * (y : ℂ) = 1) : x = 1 := by
  subst hg hy
  simp only [Pi.one_apply, Units.val_one, Matrix.det_one, map_one, one_zpow, Finset.prod_const_one, mul_one] at h
  refine Units.ext (hf (io.injective ?_))
  rw [h, Units.val_one, map_one, map_one]

set_option maxHeartbeats 1000000 in

theorem triv_of_isLocEnv : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] {N : ℕ} (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (b : Bool) (io : PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w) ≃+* ℂ) (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (rk : Fin N ≃o Fin (Vc D j).rank) (sh : D.what₂.Tau → ℤ) (Lf : IntermediateField ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) [FiniteDimensional ℚ_[Formalism.EigenvalueLevelCeiling.plc w] Lf] (kap : levJ p j (p.R.mu w) →* (D.what₂.Tau → GL (Fin N) (intR Lf))) (chi : levJ p j (p.R.mu w) →* (intR Lf)ˣ), ChoiceOk p j w e0 b io ev bs rk sh kap chi → ∀ (i : (blk p j (p.R.mu w)).Pl × ℕ), 1 ≤ i.2 → i.2 ≤ (Vc D j).rank → ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) i.1).asIdeal → ∀ u : Bridge.Gf (Vc D j), u ∈ levJ p j (p.R.mu w) → isLocEnv (Vc D j) p.R.pl (p.P.A3.A.ok (p.R.mu w)) i u → (frameOf p j (p.R.mu w) (Formalism.EigenvalueLevelCeiling.plc w) N Lf kap chi).Triv u := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j w _ N e0 b io ev bs rk sh Lf _ kap chi hC i hi1 hi2 hl u hu hloc
  obtain ⟨-, -, -, hEv, hKap, hChi⟩ := hC
  have hc : levChi p j (p.R.mu w) ⟨u, hu⟩ = 1 := (p.R.B.L j (p.R.mu w)).hecke.chi_loc i ⟨hi1, hi2⟩ ⟨u, hu⟩ hloc
  have hone : ∀ τ, (matOf j u).map (ev τ) = 1 := fun τ =>
    map_eq_one_of_isLocEnv (Vc D j) p.R.pl (p.P.A3.A.ok (p.R.mu w)) i u hloc (Formalism.EigenvalueLevelCeiling.plc w) hl (ev τ) (hEv τ).2.2.1
  have hk : kap ⟨u, hu⟩ = 1 := funext fun τ =>
    kap_eq_one (intEmb_injective Lf) (kap ⟨u, hu⟩ τ) (bs τ) ((matOf j u).map (ev τ)) rk rk.injective (hone τ) (hKap ⟨u, hu⟩ τ)
  have hx : chi ⟨u, hu⟩ = 1 :=
    chi_eq_one (intEmb_injective Lf) io (kap ⟨u, hu⟩) sh (chi ⟨u, hu⟩) (levChi p j (p.R.mu w) ⟨u, hu⟩) hk hc (hChi ⟨u, hu⟩)
  exact ⟨hu, hk, hx⟩

end GlobalTheory.FrameTriv
