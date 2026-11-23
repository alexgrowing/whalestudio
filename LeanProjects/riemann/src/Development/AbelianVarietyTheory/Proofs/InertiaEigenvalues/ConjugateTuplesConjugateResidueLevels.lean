import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResEtaHasInfExpOfIsEtaConj
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.ConjRes

section General

variable {D : D7}

theorem locK_conj {c c' : (AE D)ˣ →* Circle} {χ χ' : Formalism.L2.Host.HChar D.host.E} (h : ChrEq c χ) (h' : ChrEq c' χ')
    (τ : ℂ ≃+* ℂ) (hc : ∀ x, ((c' x : Circle) : ℂ) = τ ((c x : Circle) : ℂ)) (P : Pl D.host.E) (k : D.host.Eˣ) :
    ((χ'.locK P k : ℂˣ) : ℂ) = τ ((χ.locK P k : ℂˣ) : ℂ) := by
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  rw [← h.2 P e he k _ (Formalism.L2.JoinChr.locU_val he.1 k), ← h'.2 P e he k _ (Formalism.L2.JoinChr.locU_val he.1 k), hc]

theorem exists_lift (P : Pl D.host.E) (u : (kP P)ˣ) :
    ∃ (a : 𝓞 D.host.E) (k : D.host.Eˣ), (k : D.host.E) = a ∧ (u : kP P) = Ideal.Quotient.mk _ a := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := P.asIdeal) (u : kP P)
  have : Nontrivial (kP P) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  have h0 : (a : D.host.E) ≠ 0 := by
    intro h
    have : a = 0 := by exact_mod_cast h
    rw [this, map_zero] at ha
    exact u.ne_zero ha.symm
  exact ⟨a, Units.mk0 _ h0, rfl, ha.symm⟩

theorem unrAt_of_isRes_one {χ : Formalism.L2.Host.HChar D.host.E} {P : Pl D.host.E} (h : IsRes χ P 1) : χ.UnrAt P := by
  have key : ∀ (a : 𝓞 D.host.E) (k : D.host.Eˣ), (k : D.host.E) = a → a ∉ P.asIdeal → χ.locK P k = 1 := by
    intro a k hk ha
    have := P.isMaximal
    have hu : IsUnit (Ideal.Quotient.mk P.asIdeal a) := by
      let _ := Ideal.Quotient.field P.asIdeal
      exact (Ne.isUnit (fun h0 => ha (Ideal.Quotient.eq_zero_iff_mem.1 h0)))
    exact (h a k hu.unit hk rfl).symm
  refine GlobalTheory.EtaConjType.unrAt_of_locK χ P fun u hu => ?_
  obtain ⟨n, ⟨d, hd⟩, hnd⟩ := P.exists_primeCompl_mul_eq_of_integer (u : D.host.E) hu.le
  have hd' : d ∉ P.asIdeal := hd
  have hd0 : (d : D.host.E) ≠ 0 := by
    intro h0
    have : d = 0 := by exact_mod_cast h0
    exact hd' (this ▸ P.asIdeal.zero_mem)
  have hn : n ∉ P.asIdeal := by
    rw [← P.valuation_eq_one_iff_notMem (K := D.host.E), ← hnd, map_mul, hu, one_mul]
    exact (P.valuation_eq_one_iff_notMem (K := D.host.E)).2 hd'
  have e1 := key d (Units.mk0 _ hd0) rfl hd'
  have e2 := key n (u * Units.mk0 _ hd0) hnd hn
  rwa [map_mul, e1, mul_one] at e2

theorem levFn_conj {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) {r : ℕ} (hr : r ≤ n) (t : ℕ) (Pg : Finset (Pl D.host.E))
    {Q Q' : Finset (Pl D.host.E)} (hQ : Q' = Q) (τ : ℂ ≃+* ℂ) (χ ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (hχ : ∀ PP ∈ Pg, ∀ x, τ ((χ PP x : ℂˣ) : ℂ) = ((χ PP x : ℂˣ) : ℂ))
    (hξ : ∀ PP ∈ Q, ∀ x, ((ξ' PP x : ℂˣ) : ℂ) = τ ((ξ PP x : ℂˣ) : ℂ)) (x) :
    ((levFn β ⟨r, hr, t, 1, Pg, Q', LevelP.triv Pg r ℂ, fun _ PP => (χ PP)⁻¹, ξ'⟩ x : ℂˣ) : ℂ) =
      τ ((levFn β ⟨r, hr, t, 1, Pg, Q, LevelP.triv Pg r ℂ, fun _ PP => (χ PP)⁻¹, ξ⟩ x : ℂˣ) : ℂ) := by
  subst hQ
  have h1 : ∀ y, ext1 (LevelP.triv Pg r ℂ).H (LevelP.triv Pg r ℂ).chi y = 1 := fun y => Lev.subgroupCharExtension_one_apply _ _
  unfold levFn
  simp only [h1, one_mul, Units.val_mul, Units.coe_prod, map_mul, map_prod]
  congr 1
  · refine Finset.prod_congr rfl fun PP hP => Finset.prod_congr rfl fun c _ => ?_
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, hχ PP hP]
  · exact Finset.prod_congr rfl fun PP hP => hξ PP hP _

theorem lev_congr (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) {r : ℕ} (hr : r ≤ V.rank) (t : ℕ) (Pg : Finset (Pl D.host.E))
    {Q Q' : Finset (Pl D.host.E)} (hQ : Q' = Q) (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) :
    (levEnv V β ⟨r, hr, t, 1, Pg, Q', P, χ, ξ'⟩).J = (levEnv V β ⟨r, hr, t, 1, Pg, Q, P, χ, ξ⟩).J := by
  subst hQ
  rfl

theorem levEnv_chi (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (k : Bridge.Gf V)
    (hk : k ∈ (levEnv V β L).J) :
    (levEnv V β L).χ ⟨k, hk⟩ = levFn β (Lev.flag1L L) (Formalism.UG.bc (Lev.swapAE D) k.1) := rfl

theorem principalLevel_definite_datum_flag_eq {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) (t : T0) :
    Lev.flag1L (L.datVt i t) = ⟨D.R.r, r_le_V i, D.R.t, 1, L.Pg, L.Q t, LevelP.triv L.Pg D.R.r ℂ,
      fun _ PP => (L.chi ((i : ℕ) + 1) PP)⁻¹, L.xiR t⟩ := rfl

theorem datVt_eq {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) (t : T0) :
    L.datVt i t = ⟨D.R.r, r_le_V i, D.R.t, 1, L.Pg, L.Q t, (LevelP.triv L.Pg D.R.r ℂ).conj,
      fun _ PP => (L.chi ((i : ℕ) + 1) PP)⁻¹, L.xiR t⟩ := rfl

theorem lev_datVt {T0 : Type} (L : LevCh D T0) (i : Fin D.R.m) {t t' : T0} (h : L.Q t' = L.Q t) :
    (levEnv (Vc D i) (L.βV i) (L.datVt i t')).J = (levEnv (Vc D i) (L.βV i) (L.datVt i t)).J := by
  rw [datVt_eq, datVt_eq]
  exact lev_congr (Vc D i) (L.βV i) (r_le_V i) D.R.t L.Pg h _ _ (L.xiR t) (L.xiR t')

end General

set_option maxHeartbeats 1000000 in

theorem conj_res : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → ∀ (τ : ℂ ≃+* ℂ) (t t' : T0), ConjTup R τ t t' → (∀ PP ∈ R.Q t, ∀ x, ((R.xiR t' PP x : ℂˣ) : ℂ) = τ ((R.xiR t PP x : ℂˣ) : ℂ)) ∧ (∀ PP ∈ R.Q t, R.xiR t PP ≠ 1) ∧ (∀ P, (((R.xiH t').val P : ℂˣ) : ℂ) = τ (((R.xiH t).val P : ℂˣ) : ℂ)) ∧ ∀ i : Fin D.R.m, FixBase T R i τ → levJ R i t' = levJ R i t ∧ ∀ k (hk : k ∈ levJ R i t) (hk' : k ∈ levJ R i t'), (((levEnv (Vc D i) (R.βV i) (R.datVt i t')).χ ⟨k, hk'⟩ : ℂˣ) : ℂ) = τ (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨k, hk⟩ : ℂˣ) : ℂ) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC τ t t' hct
  have hL := hC.lev
  have hloc := locK_conj (hL.xi t) (hL.xi t') τ hct.2
  have h1 : ∀ PP ∈ R.Q t, ∀ x, ((R.xiR t' PP x : ℂˣ) : ℂ) = τ ((R.xiR t PP x : ℂˣ) : ℂ) := by
    intro PP hP x
    obtain ⟨a, k, hk, hx⟩ := exists_lift PP x
    rw [hL.xiR t PP hP a k x hk hx, hL.xiR t' PP (hct.1 ▸ hP) a k x hk hx]
    exact hloc PP k
  refine ⟨h1, fun PP hP h => ?_, fun P => hloc P _, fun i hτ => ⟨?_, fun k hk hk' => ?_⟩⟩
  · exact (hL.Q_ram t PP).2 (Or.inl hP) (unrAt_of_isRes_one (h ▸ hL.xiR t PP hP))
  · exact lev_datVt R.toLevCh i hct.1
  · rw [levEnv_chi, levEnv_chi, principalLevel_definite_datum_flag_eq, principalLevel_definite_datum_flag_eq]
    exact levFn_conj (R.βV i) (r_le_V i) D.R.t R.Pg hct.1 τ (R.chi ((i : ℕ) + 1)) (R.xiR t) (R.xiR t') hτ.chi h1 _

end GlobalTheory.ConjRes
