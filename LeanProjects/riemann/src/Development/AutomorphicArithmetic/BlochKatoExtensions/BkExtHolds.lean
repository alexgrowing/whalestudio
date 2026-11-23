import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.RealExtOfExact
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionRuleStmt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.T2SpaceLocalLatticeRepresentationSpace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardTorsionMulFinrank

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Module IsLocalRing

section Generic

open TensorProduct Formalism.MainNotions

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} {W : LocWach PD LL O v n}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

private theorem UpperTheory.Prune.bk_gen (E : EtTie W RA RW inclR φR gR πA) (e : W.DD W.one)
    (hN : W.N W.one = Submodule.span (LetA O n) {e})
    (hfree : ∀ a : LetA O n, a • e = 0 → a = 0) (t : ↥W.one.L.T)
    (ht : E.jD W.one e = (1 : RW) ⊗ₜ[O] t) (u : ↥W.one.L.T) : ∃ o : O, u = o • t := by
  obtain ⟨e₁, f₀, hf₀, hj, hN₁⟩ := E.one_e
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1
    (hf₀ ▸ Submodule.mem_top : t ∈ Submodule.span O {f₀})
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1
    (hf₀ ▸ Submodule.mem_top : u ∈ Submodule.span O {f₀})
  have he : e = c • e₁ := by
    apply E.jD_inj
    rw [map_smul, hj, ht, ← hc, TensorProduct.tmul_smul]
  have h1 : e₁ ∈ Submodule.span (LetA O n) {e} := by
    rw [← hN, hN₁]; exact Submodule.mem_span_singleton_self e₁
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h1
  have h2 : (algebraMap O (LetA O n) c * a - 1) • e = 0 := by
    rw [sub_smul, one_smul, mul_smul, ha, algebraMap_smul, ← he, sub_self]
  have h3 := congrArg (fun x : LetA O n => PowerSeries.constantCoeff (x 0)) (hfree _ h2)
  have h4 : c * PowerSeries.constantCoeff (a 0) = 1 := by
    simpa [sub_eq_zero, Algebra.algebraMap_eq_smul_one] using h3
  refine ⟨d * PowerSeries.constantCoeff (a 0), ?_⟩
  rw [← hc, smul_smul, mul_assoc, mul_comm _ c, h4, mul_one, hd]

private theorem UpperTheory.Prune.bk_ext [IsTopologicalRing LL] [FiniteDimensional Qp LL]
    (h1 : IsCrys PD W.one.ρ) (t : ↥W.one.L.T) (ht : ∀ u : ↥W.one.L.T, ∃ o : O, u = o • t)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (c : G → T.V) (hc : c ∈ latticeFiniteCocycles PD T.L) :
    ∃ (Y : LocLat G Qp LL O) (ι : LatHom T.L Y.L) (π : LatHom Y.L W.one.L),
      IsSESLat (Qp := Qp) ι π ∧ IsCrys PD Y.ρ ∧ ∃ x : ↥Y.L.T, (t : W.one.V) = π.f (x : Y.V) ∧
        ∀ g, ι.f (c g) = Y.ρ g (x : Y.V) - (x : Y.V) := by
  obtain ⟨f, lam₀, hTf, hlf, hlam₀⟩ := LiftingTheory.lext_lam W
  obtain ⟨o, ho⟩ := ht ⟨f, by rw [hTf]; exact Submodule.mem_span_singleton_self f⟩
  have ho' : f = o • (t : W.one.V) := congrArg Subtype.val ho
  let lam : W.one.V →ₗ[LL] LL := algebraMap O LL o • lam₀
  have hlt : lam t = 1 := by
    change algebraMap O LL o • lam₀ t = 1
    rw [← map_smul, algebraMap_smul, ← ho', hlf]
  have hlam : ∀ y ∈ W.one.L.T, ∃ o : O, lam y = algebraMap O LL o := by
    intro y hy
    obtain ⟨o', h'⟩ := hlam₀ y hy
    refine ⟨o * o', ?_⟩
    change algebraMap O LL o • lam₀ y = _
    rw [h', map_mul, smul_eq_mul]
  obtain ⟨x₀, hx₀⟩ := hc.2.2
  refine ⟨LiftingTheory.lext_Tp T W.one lam c hc.1 hlam, LiftingTheory.lext_ι T W.one lam c hc.1 hlam,
    LiftingTheory.lext_π T W.one lam c hc.1 hlam W.one_triv, LiftingTheory.lext_ses T W.one lam c hc.1 hlam W.one_triv,
    LiftingTheory.lext_crys T.ρ W.one.ρ _ lam c W.one_triv (fun g z => rfl) x₀ hx₀ hT h1,
    ⟨(0, t), T.L.T.zero_mem, t.2⟩, rfl, fun g => ?_⟩
  change (c g, (0 : W.one.V)) = (T.ρ g 0 + lam t • c g, (t : W.one.V)) - (0, (t : W.one.V))
  simp [hlt]

private theorem UpperTheory.Prune.bk_core [IsTopologicalRing LL] [FiniteDimensional Qp LL]
    (E : EtTie W RA RW inclR φR gR πA) (h1 : IsCrys PD W.one.ρ)
    (hker : ∀ b : TW RW W.one, TWmap φR W.one b = b → ∃ t : ↥W.one.L.T, b = (1 : RW) ⊗ₜ[O] t)
    (hF : InvariantsGenerators.FontCore W) (hX : tableLineDegreeTwo.HerrExt W E)
    (hH : ∀ (T : LocLat G Qp LL O) (pr : W.wachCocyclesDelta T), W.clK T pr = 0 →
      ∃ m, (∀ δ ∈ W.DelF, W.γD T δ m = m) ∧
        (pr : W.DD T × W.DD T) = (W.φD T m - m, W.γD T W.gamK m - m))
    (d : O) (hd : d * (W.DelF.card : O) = 1) (e : W.DD W.one)
    (hN : W.N W.one = Submodule.span (LetA O n) {e}) (hφ : W.φD W.one e = e)
    (hγ : ∀ g, W.γD W.one g e = e) (hfree : ∀ a : LetA O n, a • e = 0 → a = 0) : BKExt W e := by
  intro T hT w hw
  obtain ⟨c, hc, hcf, hcw⟩ := (LiftingTheory.liftb_mem_H1fT PD T _).1 hw
  obtain ⟨t, ht⟩ := hker (E.jD W.one e) (by rw [← E.jD_φ, hφ])
  obtain ⟨Y, ι, π, hs, hY, x, hx, hcx⟩ :=
    UpperTheory.Prune.bk_ext h1 t (UpperTheory.Prune.bk_gen E e hN hfree t ht) T hT c hcf
  obtain ⟨hi, hsu, hex⟩ := hF.2.1 T Y W.one ι π hs
  refine ⟨Y, ι, π, hs, ⟨Y.fdim, Y.mtop, Y.cont, hY⟩, hi, hex, ?_⟩
  obtain ⟨E₁, hE₁⟩ := hsu e
  let E₀ := LiftingTheory.lifta_avg W Y d E₁
  have hΔ : ∀ δ ∈ W.DelF, W.γD Y δ E₀ = E₀ := LiftingTheory.lifta_avg_inv W Y d E₁
  have hπ : W.map π E₀ = e := by
    rw [LiftingTheory.lifta_avg_map, hE₁, LiftingTheory.lifta_avg_fix W _ d hd e (fun δ _ => hγ δ)]
  obtain ⟨y, hy⟩ := (hex (W.φD Y E₀ - E₀)).1 (by rw [map_sub, W.map_φ, hπ, hφ, sub_self])
  obtain ⟨z, hz⟩ := (hex (W.γD Y W.gamK E₀ - E₀)).1 (by rw [map_sub, W.map_γ, hπ, hγ, sub_self])
  have hp : (y, z) ∈ W.wachCocyclesDelta T := by
    refine (LiftingTheory.lifta_mem_Z1DΔ W T y z).2 ⟨GlobalTheory.HerrClass.mem_herrCocycles_of_eq _ _ y z (hi ?_), fun δ hδ =>
      ⟨hi ?_, hi ?_⟩⟩
    · rw [map_sub, map_sub, W.map_γ, W.map_φ, hy, hz, map_sub, map_sub, W.φγ_comm]
      abel
    · rw [W.map_γ, hy, map_sub, ← W.φγ_comm, hΔ δ hδ]
    · rw [W.map_γ, hz, map_sub, ← W.γD_mul, mul_comm, W.γD_mul, hΔ δ hδ]
  obtain ⟨c', hc', hcx'⟩ := hX.2 T Y ι π hs x t hx E₀ hΔ (by rw [hπ, ht]) ⟨(y, z), hp⟩ hy hz
  have hcc : c' = ⟨c, hc⟩ := Subtype.ext (funext fun g => hs.1 (by rw [hcx', hcx]))
  have h0 : W.clK T (w - (⟨(y, z), hp⟩ : ↥(W.wachCocyclesDelta T)) : ↥(W.wachCocyclesDelta T)) = 0 :=
    (map_sub (W.clK T) w ⟨(y, z), hp⟩).trans
      (sub_eq_zero.2 (hcw.symm.trans ((congrArg _ hcc.symm).trans hc')))
  obtain ⟨m, hm, hmw⟩ := hH T _ h0
  have e1 : (w : W.DD T × W.DD T).1 - y = W.φD T m - m := congrArg Prod.fst hmw
  have e2 : (w : W.DD T × W.DD T).2 - z = W.γD T W.gamK m - m := congrArg Prod.snd hmw
  refine ⟨E₀ + W.map ι m, fun δ hδ => ?_, ?_, ?_, ?_⟩
  · rw [map_add, hΔ δ hδ, ← W.map_γ, hm δ hδ]
  · rw [map_add, hπ, (hex _).2 ⟨m, rfl⟩, add_zero]
  · rw [sub_eq_iff_eq_add.1 e1, map_add, map_sub, hy, map_add, W.map_φ]
    abel
  · rw [sub_eq_iff_eq_add.1 e2, map_add, map_sub, hz, map_add, W.map_γ]
    abel

end Generic

theorem UpperTheory.Prune.bkExt_holds :
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (h9 : Formalism.MainNotions.LocalSituation.adm9 D HW F) (hFont : Formalism.MainNotions.InvariantsGenerators.LitFont D HW F)
    (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL) (h5 : 5 ≤ l) (e) (he : UnitGen ((HW l).W K 1 LL h.2.2) e),
    BKExt ((HW l).W K 1 LL h.2.2) e := by
  intro D HW F h9 hFont l _ K LL h h5 e he
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have hc := GlobalTheory.TorsionCard.card_torsion_mul_finrank (D.loc l) K LL ((HW l).W K 1 LL h.2.2) h.2.1
    h.2.2.2.2.1
  have hu : IsUnit (((l - 1 : ℕ)) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  have hu' := hu.map (algebraMap ℤ_[l] ↥(OL LL))
  rw [map_natCast, ← hc, Nat.cast_mul] at hu'
  obtain ⟨d, hd⟩ := (isUnit_of_mul_isUnit_left hu').exists_left_inv
  have hH := (GlobalTheory.HerrClass.herr_a D HW F h9 l K 1 LL h.2.2).1
    (fun h2 => absurd (((D.loc l).PD_p K).symm.trans h2) h.2.1)
  exact UpperTheory.Prune.bk_core ((F l).E K 1 LL h.2.2).tie
    (Formalism.MainNotions.LiftingTheory.lone_HOne0_holds D HW F l K 1 LL h.2.2).1
    ((h9 l K 1 LL h.2.2).1 _).2.1 (hFont l K LL h)
    (GlobalTheory.ExtDict.extension_rule D HW F l K LL h)
    (fun T pr h0 => ((hH T).2.1 pr).1 h0) d hd e he.1 he.2.1 he.2.2.1 he.2.2.2
