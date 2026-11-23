import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCompatFiniteIsometry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentPreservesLatticeHat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.SphTrans

open GlobalTheory.HeckeTrans

section Abstract

variable {R : Type} [CommRing R] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable {f : R} {J : Matrix m n R} {J' : Matrix n m R} {M : Matrix n n R} {M' : Matrix m m R}
variable {L : AddSubgroup (n → R)} {L' : AddSubgroup (m → R)}

omit [Fintype m] [DecidableEq m] in
theorem mem_iff_parts (loc' : ∀ y ∈ L', f • y ∈ L') (y : m → R) : y ∈ L' ↔ f • y ∈ L' ∧ y - f • y ∈ L' :=
  ⟨fun h => ⟨loc' y h, L'.sub_mem h (loc' y h)⟩, fun h => by simpa using L'.add_mem h.1 h.2⟩

theorem stab_iff_conj (h1 : J * J' = 1) (h2 : J' * J = 1) (hc : M' * J = J * M)
    (hL : ∀ y, f • y ∈ L ↔ f • J.mulVec y ∈ L') (loc' : ∀ y ∈ L', f • y ∈ L') (hs : f • (M' - 1) = M' - 1)
    (h : ∀ y, y ∈ L ↔ M.mulVec y ∈ L) (y : m → R) : y ∈ L' ↔ M'.mulVec y ∈ L' := by
  have e1 : M'.mulVec y - f • M'.mulVec y = y - f • y := by
    have := congrArg (fun A => Matrix.mulVec A y) hs
    simp only [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, smul_sub] at this
    linear_combination (exp := 1) -this
  rw [mem_iff_parts loc' y, mem_iff_parts loc' (M'.mulVec y), e1, lat_inv h1 hL y, lat_inv h1 hL (M'.mulVec y),
    Matrix.mulVec_mulVec, ← conj_inv h1 h2 hc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul M, ← h]

end Abstract

section Coset

variable {D : D7} {V V' : HSp D}

theorem cosetRep_transfer (Φ : GfC V ≃* GfC V') {K : Set (GA D V)} {K' : Set (GA D V')} (hK : ∀ k ∈ K, k ∈ GfC V)
    (hK' : ∀ k ∈ K', k ∈ GfC V') (hKK : ∀ k : GfC V, (k : GA D V) ∈ K ↔ (Φ k : GA D V') ∈ K')
    {R : Finset (GA D V)} {R' : Finset (GA D V')} (hR' : ∀ k ∈ R', k ∈ GfC V')
    (hRR : ∀ k : GfC V, (k : GA D V) ∈ R ↔ (Φ k : GA D V') ∈ R') (α : GfC V) (h : IsCosetRep V K α R) :
    IsCosetRep V' K' (Φ α) R' := by
  obtain ⟨ha, hb⟩ := h
  constructor
  · intro γ' hγ'
    refine ⟨hR' _ hγ', ?_⟩
    obtain ⟨γ, hγ⟩ := Φ.surjective ⟨γ', hR' _ hγ'⟩
    obtain rfl : γ' = (Φ γ : GA D V') := by rw [hγ]
    obtain ⟨-, k₁, h₁, k₂, h₂, e⟩ := ha _ ((hRR γ).2 hγ')
    refine ⟨_, (hKK ⟨k₁, hK _ h₁⟩).1 h₁, _, (hKK ⟨k₂, hK _ h₂⟩).1 h₂, ?_⟩
    have e' : γ = ⟨k₁, hK _ h₁⟩ * α * ⟨k₂, hK _ h₂⟩ := Subtype.ext e
    rw [e', map_mul, map_mul]
    rfl
  · rintro x ⟨k₁', h₁, k₂', h₂, rfl⟩
    obtain ⟨k₁, e₁⟩ := Φ.surjective ⟨k₁', hK' _ h₁⟩
    obtain rfl : k₁' = (Φ k₁ : GA D V') := by rw [e₁]
    obtain ⟨k₂, e₂⟩ := Φ.surjective ⟨k₂', hK' _ h₂⟩
    obtain rfl : k₂' = (Φ k₂ : GA D V') := by rw [e₂]
    obtain ⟨γ, ⟨hγ, hx⟩, hu⟩ := hb _ ⟨_, (hKK k₁).2 h₁, _, (hKK k₂).2 h₂, rfl⟩
    have key : ∀ g : GfC V, ((g : GA D V)⁻¹ * (k₁ * α * k₂) ∈ K) ↔
        ((Φ g : GA D V')⁻¹ * (Φ k₁ * Φ α * Φ k₂) ∈ K') := fun g => by
      have := hKK (g⁻¹ * (k₁ * α * k₂))
      rw [map_mul, map_mul, map_mul, map_inv] at this
      exact this
    refine ⟨Φ ⟨γ, (ha γ hγ).1⟩, ⟨(hRR ⟨γ, _⟩).1 hγ, (key ⟨γ, _⟩).1 hx⟩, ?_⟩
    rintro γ' ⟨h3, h4⟩
    obtain ⟨g, e₃⟩ := Φ.surjective ⟨γ', hR' _ h3⟩
    obtain rfl : γ' = (Φ g : GA D V') := by rw [e₃]
    have : g = ⟨γ, (ha γ hγ).1⟩ := Subtype.ext (hu g ⟨(hRR g).2 h3, (key g).2 h4⟩)
    rw [this]

end Coset

section Div

variable {R : Type} [CommRing R] {m n : ℕ}

theorem div_conj (hr : m = n) {e f : R} {J : Matrix (Fin m) (Fin n) R} {J' : Matrix (Fin n) (Fin m) R}
    {M : Matrix (Fin n) (Fin n) R} {M' : Matrix (Fin m) (Fin m) R} {L : AddSubgroup (Fin n → R)} {L' : AddSubgroup (Fin m → R)}
    (S : AddSubgroup R) (c : ℕ → R) (hef : e * f = e) (h1 : J * J' = 1) (hc : M' * J = J * M)
    (hL : ∀ y, f • y ∈ L ↔ f • J.mulVec y ∈ L') (loc : ∀ y ∈ L, f • y ∈ L) (loc' : ∀ y ∈ L', f • y ∈ L')
    (h : ∃ B : Matrix (Fin n) (Fin n) R, (∀ z : Fin n → R, (∀ i, z i ∈ S) → e • B.mulVec z ∈ L) ∧
      (∀ y ∈ L, ∃ z : Fin n → R, (∀ i, z i ∈ S) ∧ e • y = e • B.mulVec z) ∧
      (∀ y ∈ L, ∃ z : Fin n → R, (∀ i, z i ∈ S) ∧ e • M.mulVec y = e • B.mulVec fun i => c i.1 * z i) ∧
      ∀ z : Fin n → R, (∀ i, z i ∈ S) → ∃ y ∈ L, e • M.mulVec y = e • B.mulVec fun i => c i.1 * z i) :
    ∃ B : Matrix (Fin m) (Fin m) R, (∀ z : Fin m → R, (∀ i, z i ∈ S) → e • B.mulVec z ∈ L') ∧
      (∀ y ∈ L', ∃ z : Fin m → R, (∀ i, z i ∈ S) ∧ e • y = e • B.mulVec z) ∧
      (∀ y ∈ L', ∃ z : Fin m → R, (∀ i, z i ∈ S) ∧ e • M'.mulVec y = e • B.mulVec fun i => c i.1 * z i) ∧
      ∀ z : Fin m → R, (∀ i, z i ∈ S) → ∃ y ∈ L', e • M'.mulVec y = e • B.mulVec fun i => c i.1 * z i := by
  subst hr
  obtain ⟨B, a1, a2, a3, a4⟩ := h
  have hfe : f * e = e := by rw [mul_comm, hef]
  refine ⟨J * B, fun z hz => ?_, fun y hy => ?_, fun y hy => ?_, fun z hz => ?_⟩
  · have := (hL (e • B.mulVec z)).1 (loc _ (a1 z hz))
    rwa [Matrix.mulVec_smul, smul_smul, hfe, Matrix.mulVec_mulVec] at this
  · obtain ⟨z, hz, e2⟩ := a2 _ ((lat_inv h1 hL y).1 (loc' y hy))
    refine ⟨z, hz, ?_⟩
    have := congrArg J.mulVec e2
    rwa [smul_smul, hef, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h1,
      Matrix.one_mulVec] at this
  · obtain ⟨z, hz, e2⟩ := a3 _ ((lat_inv h1 hL y).1 (loc' y hy))
    refine ⟨z, hz, ?_⟩
    have := congrArg J.mulVec e2
    rwa [Matrix.mulVec_smul M, smul_smul, hef, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← conj_eq h1 hc] at this
  · obtain ⟨y, hy, e2⟩ := a4 z hz
    refine ⟨_, (hL y).1 (loc y hy), ?_⟩
    have := congrArg J.mulVec e2
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hc] at this
    rw [Matrix.mulVec_smul, smul_smul, hef, Matrix.mulVec_mulVec]
    exact this

end Div

variable {D : D7}

theorem mul_of_isPrimeIdem {P : Pl D.host.E} {e f : Formalism.L2.Theta.AE D} (h : IsPrimeIdem P e f) (hf : f * f = f) :
    e * f = e := by
  rcases h with ⟨h, rfl⟩ | ⟨rfl, -⟩
  · rw [mul_add, h.1.1, h.1.2.1, add_zero]
  · exact hf

theorem suppF_iff (f : Formalism.L2.Theta.AE D) {V : HSp D} {α : GA D V} (hα : α ∈ GfC V) :
    SuppF V f α ↔ finPart D f • (finMat D.sp.cm.sig V.gram α - 1) = finMat D.sp.cm.sig V.gram α - 1 := by
  rw [finMat_eq, supp_map_iff]
  refine ⟨fun hs i j => congrArg (finPart D) (hs i j), fun hs i j => ?_⟩
  have hs4 := (supp_map_iff (infPart D) f (mt V α)).1 (by rw [inf_eq hα, sub_self, smul_zero])
  exact GlobalTheory.SplitScalar.adele_ext (hs4 i j) (hs i j)

set_option maxHeartbeats 800000 in

theorem lamHat_loc (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ)
    {P : Pl D.host.E} {e f : Formalism.L2.Theta.AE D} (hB : IsBaseFrame V β Λ N) (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hP : IsPrimeIdem P e f) (hff : f * f = f) (y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    (y ∈ Formalism.L2.NTheta.LamHat V → (fun a => finPart D f * y a) ∈ Formalism.L2.NTheta.LamHat V) ∧
      ((fun a => finPart D f * y a) ∈ Formalism.L2.NTheta.LamHat V ↔
        ∀ i, (β⁻¹).val.mulVec (fun a => swapAE D (finPart D f * y a)) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) := by
  obtain ⟨hfr, -, -, h01, h10⟩ := hB
  have key : ∀ z, z ∈ Formalism.L2.NTheta.LamHat V ↔
      (fun i => swapAE D (z i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (GlobalTheory.LevSplit.L0sub V) :=
    fun z => GlobalTheory.LevSplit.latHat_iff (GlobalTheory.LevSplit.L0sub V) z
  obtain ⟨u, hu⟩ := GlobalTheory.LevSplit.idem_div_int hP N N (by simp) hN hN
  have hu' : (u : Lev.EAf D) * (N : Lev.EAf D) = GlobalTheory.LevSplit.finSw D f := by
    rw [← hu, map_natCast]; rfl
  obtain ⟨φ, hφ'⟩ : ∃ φ : Formalism.L2.Herm.intAf D.host.F D.host.E, (φ : Lev.EAf D) = GlobalTheory.LevSplit.finSw D f :=
    ⟨u * oToS D.host.F D.host.E N, hu⟩
  have hε : GlobalTheory.LevSplit.finSw D f * GlobalTheory.LevSplit.finSw D f = GlobalTheory.LevSplit.finSw D f := by
    rw [← map_mul, hff]
  have hsw : (fun a => swapAE D (finPart D f * y a)) = fun a => GlobalTheory.LevSplit.finSw D f * swapAE D (y a) :=
    funext fun a => map_mul _ _ _
  have a01 := GlobalTheory.LevSplit.hatL_smul (F := D.host.F) (GlobalTheory.LevSplit.L0sub V) Λ N h01
  have a10 := GlobalTheory.LevSplit.hatL_smul (F := D.host.F) Λ (GlobalTheory.LevSplit.L0sub V) N h10
  constructor
  · intro hy
    refine (key _).2 ?_
    rw [hsw, ← hφ']
    exact Submodule.smul_mem _ φ ((key y).1 hy)
  · refine (key _).trans (Iff.trans ?_ (hfr _))
    rw [hsw]
    exact ⟨GlobalTheory.LatLoc.loc_transfer _ _ N u _ hu' hε a01 _, GlobalTheory.LatLoc.loc_transfer _ _ N u _ hu' hε a10 _⟩

set_option maxHeartbeats 800000 in

theorem transfer {V V' : HSp D} (hr : V'.rank = V.rank) {P : Pl D.host.E}
    (J : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))
    (J' : Matrix (Fin V.rank) (Fin V'.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))
    (h1 : HMul.hMul J J' = 1) (h2 : HMul.hMul J' J = 1) (Φ : GfC V ≃* GfC V')
    (hc : ∀ g : GfC V, HMul.hMul (finMat D.sp.cm.sig V'.gram (Φ g : GA D V')) J =
      HMul.hMul J (finMat D.sp.cm.sig V.gram (g : GA D V)))
    (hL : ∀ e f, IsPrimeIdem P e f →
      ∀ y, finPart D f • y ∈ Formalism.L2.NTheta.LamHat V ↔ finPart D f • J.mulVec y ∈ Formalism.L2.NTheta.LamHat V')
    (loc : ∀ e f, IsPrimeIdem P e f → ∀ y ∈ Formalism.L2.NTheta.LamHat V, finPart D f • y ∈ Formalism.L2.NTheta.LamHat V)
    (loc' : ∀ e f, IsPrimeIdem P e f → ∀ y ∈ Formalism.L2.NTheta.LamHat V', finPart D f • y ∈ Formalism.L2.NTheta.LamHat V')
    {R : Finset (GA D V)} {R' : Finset (GA D V')} (hR' : ∀ k ∈ R', k ∈ GfC V')
    (hRR : ∀ k : GfC V, (k : GA D V) ∈ R ↔ (Φ k : GA D V') ∈ R') {d : List ℤ} (h : GlobalTheory.Hk3.SphOp V P d R) :
    GlobalTheory.Hk3.SphOp V' P d R' := by
  obtain ⟨e, f, ϖ, α, hO, hP, p1, p2, hd, -, -, hα, ⟨hlen, hdiv⟩, hR, hC⟩ := h
  obtain ⟨-, -, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
  obtain ⟨hff, -, hG, -⟩ := T3 P e f hP
  have hef : finPart D e * finPart D f = finPart D e := by rw [← RingHom.map_mul, mul_of_isPrimeIdem hP hff]
  have hc' := fun g => conj_inv h1 h2 (hc g)
  have hS : ∀ g : GfC V, SuppF V f g ↔ SuppF V' f (Φ g) := fun g => by
    rw [suppF_iff f g.2, suppF_iff f (Φ g).2]
    exact ⟨supp_conj h1 (hc g), supp_conj h2 (hc' g)⟩
  refine ⟨e, f, ϖ, Φ ⟨α, hG α hα⟩, hO, hP, p1, p2, hd, fun _ _ => Iff.rfl, fun _ _ _ => rfl, (hS ⟨α, _⟩).1 hα,
    ⟨hlen.trans hr.symm, ?_⟩, fun γ' hγ' => ?_, ?_⟩
  · exact div_conj hr (intAE D) (fun i => finPart D (incA D ((ϖ : D.host.E) ^ (d.getD i 0)))) hef h1
      (hc ⟨α, hG α hα⟩) (hL e f hP) (loc e f hP) (loc' e f hP) hdiv
  · obtain ⟨g, e₃⟩ := Φ.surjective ⟨γ', hR' _ hγ'⟩
    obtain rfl : γ' = (Φ g : GA D V') := by rw [e₃]
    exact (hS g).1 (hR _ ((hRR g).2 hγ'))
  · refine cosetRep_transfer Φ (fun k hk => hk.1.1) (fun k hk => hk.1.1) (fun k => ?_) hR' hRR ⟨α, hG α hα⟩ hC
    constructor
    · rintro ⟨⟨-, a, -⟩, b⟩
      have b' := (hS k).1 b
      exact ⟨⟨(Φ k).2, stab_iff_conj h1 h2 (hc k) (hL e f hP) (loc' e f hP) ((suppF_iff f (Φ k).2).1 b') a,
        fun v hv => absurd hv (Finset.notMem_empty v)⟩, b'⟩
    · rintro ⟨⟨-, a, -⟩, b⟩
      have b' := (hS k).2 b
      exact ⟨⟨k.2, stab_iff_conj h2 h1 (hc' k) (lat_inv h1 (hL e f hP)) (loc e f hP) ((suppF_iff f k.2).1 b') a,
        fun v hv => absurd hv (Finset.notMem_empty v)⟩, b'⟩

set_option maxHeartbeats 800000 in

theorem sphOp_iff : ∀ {D : D7} (V V' : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (β' : GL (Fin V'.rank) (Lev.EAf D)) (Pg : Finset (Pl D.host.E)) (j : Matrix (Fin V'.rank) (Fin V.rank) (Lev.EAf D)) (Φ : GfC V ≃ₜ* GfC V') (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)) (N N' : ℕ), IsBaseFrame V β Λ N → IsBaseFrame V' β' Λ' N' → GlobalTheory.CuspMult.IsFinIso V V' β β' Pg j Φ → ∀ (P : Pl D.host.E), ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ((N' : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ∀ (d : List ℤ) (B : Finset (GfC V)), GlobalTheory.Hk3.SphOp V P d (B.map ⟨Subtype.val, Subtype.val_injective⟩) ↔ GlobalTheory.Hk3.SphOp V' P d ((B.map Φ.toEquiv.toEmbedding).map ⟨Subtype.val, Subtype.val_injective⟩) := by
  intro D V V' β β' Pg j Φ Λ Λ' N N' hB hB' hI P hN hN' d B
  obtain ⟨hr, u, hu, -⟩ := hI.frame
  obtain ⟨⟨j', h1, h2⟩, hlat⟩ := frame_inv (Formalism.L2.Herm.intAf D.host.F D.host.E) β β' (finCongr hr)
    (intGL D.host.F D.host.E V'.rank u) u.val (u⁻¹).val rfl rfl j hu
  have h1' := map_mul_one (unswap D) h1
  have h2' := map_mul_one (unswap D) h2
  have hc : ∀ g : GfC V, HMul.hMul (finMat D.sp.cm.sig V'.gram (Φ g : GA D V')) (j.map (unswap D)) =
      HMul.hMul (j.map (unswap D)) (finMat D.sp.cm.sig V.gram (g : GA D V)) := fun g => by
    have hc := map_conj (unswap D) (hI.conj g)
    rwa [finE_unswap, finE_unswap] at hc
  obtain ⟨-, -, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
  have hff : ∀ e f, IsPrimeIdem P e f → f * f = f := fun e f h => (T3 P e f h).1
  have hL : ∀ e f, IsPrimeIdem P e f → ∀ y, finPart D f • y ∈ Formalism.L2.NTheta.LamHat V ↔
      finPart D f • (j.map (unswap D)).mulVec y ∈ Formalism.L2.NTheta.LamHat V' := by
    intro e f he y
    refine ((lamHat_loc V β Λ N hB hN he (hff e f he) y).2.trans (hlat _)).trans
      (Iff.trans ?_ (lamHat_loc V' β' Λ' N' hB' hN' he (hff e f he) _).2.symm)
    rw [mulVec_map_inv (unswap D) (swapAE D) swap_unswap]
  have loc : ∀ e f, IsPrimeIdem P e f → ∀ y ∈ Formalism.L2.NTheta.LamHat V, finPart D f • y ∈ Formalism.L2.NTheta.LamHat V :=
    fun e f he y => (lamHat_loc V β Λ N hB hN he (hff e f he) y).1
  have loc' : ∀ e f, IsPrimeIdem P e f → ∀ y ∈ Formalism.L2.NTheta.LamHat V', finPart D f • y ∈ Formalism.L2.NTheta.LamHat V' :=
    fun e f he y => (lamHat_loc V' β' Λ' N' hB' hN' he (hff e f he) y).1
  have hRR : ∀ k : GfC V, (k : GA D V) ∈ B.map ⟨Subtype.val, Subtype.val_injective⟩ ↔
      (Φ k : GA D V') ∈ (B.map Φ.toEquiv.toEmbedding).map ⟨Subtype.val, Subtype.val_injective⟩ := fun k =>
    (Finset.mem_map' (⟨Subtype.val, Subtype.val_injective⟩ : GfC V ↪ GA D V)).trans
      ((Finset.mem_map' Φ.toEquiv.toEmbedding).symm.trans
        (Finset.mem_map' (⟨Subtype.val, Subtype.val_injective⟩ : GfC V' ↪ GA D V')).symm)
  constructor
  · refine transfer hr.symm _ _ h1' h2' Φ.toMulEquiv hc hL loc loc' (fun k hk => ?_) hRR
    obtain ⟨g, -, rfl⟩ := Finset.mem_map.1 hk
    exact g.2
  · refine transfer hr _ _ h2' h1' Φ.toMulEquiv.symm (fun g => ?_) (fun e f he => lat_inv h1' (hL e f he)) loc' loc
      (fun k hk => ?_) (fun k => ?_)
    · obtain ⟨g, rfl⟩ := Φ.toMulEquiv.surjective g
      rw [MulEquiv.symm_apply_apply]
      exact conj_inv h1' h2' (hc g)
    · obtain ⟨g, -, rfl⟩ := Finset.mem_map.1 hk
      exact g.2
    · obtain ⟨g, rfl⟩ := Φ.toMulEquiv.surjective k
      rw [MulEquiv.symm_apply_apply]
      exact (hRR g).symm

end GlobalTheory.SphTrans

end
