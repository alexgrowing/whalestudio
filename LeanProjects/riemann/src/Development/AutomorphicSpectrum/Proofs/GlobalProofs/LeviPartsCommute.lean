import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsKInfEqMul
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryAdelicIwasawaCompactStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MinimalParabolicUnipotentLeviDecompStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicBlockEmbeddingCompactStatement
import GroundTheory.PAdicHodge.NormalizedTrace
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EvaluationMap

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Sep

open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.KInf GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped Pointwise

theorem exists_finset_cosets {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {K : Set G}
    (hK : IsCompact K) {U : Subgroup G} (hU : IsOpen (U : Set G)) :
    ∃ C : Finset G, (C : Set G) ⊆ K ∧ ∀ k ∈ K, ∃ c ∈ C, ∃ u ∈ U, k = c * u := by
  classical
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun k : K => (k : G) • (U : Set G)) (fun k => hU.smul _)
    fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, ⟨1, U.one_mem, mul_one x⟩⟩
  refine ⟨t.image Subtype.val, by simp, fun k hk => ?_⟩
  obtain ⟨c, hc, hkc⟩ := Set.mem_iUnion₂.1 (ht hk)
  obtain ⟨u, hu, e⟩ := Set.mem_smul_set.1 hkc
  exact ⟨c, Finset.mem_image_of_mem _ hc, u, hu, e.symm⟩

theorem kInf_mem_GinfC {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam θ) {V : HSp D}
    {ε : D.what₂.Tau → Fin V.rank → Bool} {fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} (hfr : IsFrameFam V ε fr)
    (κ : ∀ τ, Formalism.REAL.KG (ε τ)) : kInf θ V ε fr κ ∈ GinfC V := by
  refine list_prod_mem fun x hx => ?_
  obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
  exact (isAtTau_kAt θ V hθ τ (hfr τ).1 (hfr τ).2 (κ τ)).1

theorem mul_mem_minPar {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n r : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {X : Matrix (Fin n) (Fin r) E} {p q : GlobalTheory.AdelicU.GAd σ J}
    (hp : p ∈ PositivityTheory.ThKR.minPar σ J X) (hq : q ∈ PositivityTheory.ThKR.minPar σ J X) : p * q ∈ PositivityTheory.ThKR.minPar σ J X := by
  obtain ⟨B, hB, eB⟩ := hp
  obtain ⟨B', hB', eB'⟩ := hq
  refine ⟨B * B', hB.mul hB', ?_⟩
  rw [map_mul, Units.val_mul, Matrix.mul_assoc, eB', ← Matrix.mul_assoc, eB, Matrix.mul_assoc]

theorem exists_iwasawa : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∃ K : Subgroup (GA D V), IsCompact (K : Set (GA D V)) ∧ K ≤ GfC V ∧ ∀ g : GA D V, ∃ p ∈ PositivityTheory.ThKR.minPar D.sp.cm.sig V.gram X, ∃ κ : (∀ τ, Formalism.REAL.KG (ε τ)), ∃ k ∈ K, g = p * GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.KInf.kInf θ V ε fr κ * k := by
  intro D θ hθ V ε fr hfr m X Y hW
  have hh := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  obtain ⟨K, hKf, hK, hiw, -⟩ := GlobalTheory.T.unitary_adelic_iwasawa_compact D.host.F D.host.E D.sp.cm.sig hh.1 V.rank V.gram (hh.2 V) m X Y hW
  refine ⟨K, hK, hKf, fun g => ?_⟩
  obtain ⟨p, hp, κ, e1⟩ := GlobalTheory.T.archimedean_iwasawa_minimal_parabolic D θ hθ V ε fr hfr m X Y hW _ (GlobalTheory.AutMult.toInf V g).2
  obtain ⟨q, hq, hqf, k, hk, e2⟩ := hiw _ (GlobalTheory.AutMult.toFin V g).2
  refine ⟨p * q, mul_mem_minPar hp hq, κ, k, hk, ?_⟩
  have hcomm := GlobalTheory.AutMult.commute_inf_fin (⟨_, kInf_mem_GinfC hθ hfr κ⟩ : GinfC V) ⟨q, hqf⟩
  rw [← GlobalTheory.AutMult.toInf_mul_toFin g, e1, e2, mul_assoc p, ← mul_assoc _ q k, hcomm.eq]
  simp only [mul_assoc]

theorem exists_decomp : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ T : Finset (Fin m), ∃ C : Finset (GA D V), ∀ g : GA D V, ∃ n ∈ unip D.sp.cm.sig V.gram X T, ∃ l ∈ levi D.sp.cm.sig V.gram X Y T, ∃ c ∈ C, ∃ κ : (∀ τ, Formalism.REAL.KG (ε τ)), ∃ u ∈ U, u ∈ GfC V ∧ g = n * l * c * GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.KInf.kInf θ V ε fr κ * u := by
  intro D θ hθ V U hU ε fr hfr m X Y hW T
  classical
  have hh := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  obtain ⟨K, hK, hKf, hiw⟩ := exists_iwasawa D θ hθ V ε fr hfr m X Y hW
  obtain ⟨C, hCK, hC⟩ := exists_finset_cosets hK hU
  refine ⟨C, fun g => ?_⟩
  obtain ⟨p, hp, κ, k, hk, rfl⟩ := hiw g
  obtain ⟨c, hc, u, hu, rfl⟩ := hC k hk
  obtain ⟨n, hn, l, hl, rfl⟩ := GlobalTheory.T.minimal_parabolic_unipotent_levi_decomp D.host.F D.host.E D.sp.cm.sig hh.1 V.rank V.gram (hh.2 V) m X Y hW T p hp
  have hcf : c ∈ GfC V := hKf (hCK hc)
  have huf : u ∈ GfC V := by
    have := mul_mem (inv_mem hcf) (hKf hk)
    rwa [inv_mul_cancel_left] at this
  refine ⟨n, hn, l, hl, c, hc, κ, u, hu, huf, ?_⟩
  have hcomm := GlobalTheory.AutMult.commute_inf_fin (⟨_, kInf_mem_GinfC hθ hfr κ⟩ : GinfC V) ⟨c, hcf⟩
  simp only [mul_assoc]
  rw [← mul_assoc (kInf θ V ε fr κ) c u, hcomm.eq, mul_assoc]

theorem finiteDimensional_coeffSpan {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) :=
  _root_.UpperTheory.Reformulated.B.EvaluationMap.main ρ

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
  {ε : D.what₂.Tau → Fin V.rank → Bool} {fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}

open Classical in

theorem eq_zero_of_kInf {W : D.what₂.Tau → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)]
    {ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)} (hθ : IsInfFam θ) (hfr : IsFrameFam V ε fr) {φ : GA D V → ℂ}
    (htype : ∀ τ, HasTypeAt θ V τ (ε τ) (fr τ) (ρ τ) φ) (S : ∀ τ, Finset (Formalism.REAL.KG (ε τ)))
    (hS : ∀ τ, ∀ f ∈ GlobalTheory.Published.AutFin.coeffSpan (ρ τ), (∀ x ∈ S τ, f x = 0) → f = 0) (x : GA D V)
    (h : ∀ s ∈ Fintype.piFinset S, φ (x * kInf θ V ε fr s) = 0) (κ : ∀ τ, Formalism.REAL.KG (ε τ)) :
    φ (x * kInf θ V ε fr κ) = 0 := by
  classical
  suffices key : ∀ I : Finset D.what₂.Tau, ∀ κ : ∀ τ, Formalism.REAL.KG (ε τ), (∀ τ, τ ∉ I → κ τ ∈ S τ) →
      φ (x * kInf θ V ε fr κ) = 0 from key Finset.univ κ (by simp)
  intro I
  induction I using Finset.induction_on with
  | empty => exact fun κ hκ => h κ (Fintype.mem_piFinset.2 fun τ => hκ τ (by simp))
  | insert a I _ ih =>
    intro κ hκ
    obtain ⟨y, hy⟩ := exists_kInf_eq_mul hθ hfr κ a
    have h0 := hS a _ (htype a (x * y)) fun t ht => by
      have e := hy (Function.update κ a t) fun τ hτ => Function.update_of_ne hτ _ _
      rw [Function.update_self] at e
      show φ (x * y * kAt θ V a (ε a) (fr a) t) = 0
      rw [mul_assoc, ← e]
      refine ih _ fun τ hτ => ?_
      by_cases e' : τ = a
      · subst e'; simpa using ht
      · rw [Function.update_of_ne e']; exact hκ τ (by simp [e', hτ])
    rw [hy κ fun _ _ => rfl, ← mul_assoc]
    exact congrFun h0 (κ a)

theorem exists_finset_sep_levi : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)), (∀ τ, IsContRep (ρ τ)) → ∀ (c : D.what₂.Tau → ℕ → ℂ) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ T : Finset (Fin m), T.Nonempty → ∃ B : Finset (GA D V), ∀ φ ∈ formsOn θ V X Y T U ε fr ρ c, (∀ b ∈ B, ∀ g ∈ levi D.sp.cm.sig V.gram X Y T, φ (g * b) = 0) → φ = 0 := by
  intro D θ hθ V U hU ε fr hfr W _ _ _ ρ hρ c m X Y hW T hT
  classical
  obtain ⟨C, hC⟩ := exists_decomp D θ hθ V U hU ε fr hfr m X Y hW T
  haveI := fun τ => finiteDimensional_coeffSpan (ρ τ)
  choose S hS using fun τ => exists_finset_sep (GlobalTheory.Published.AutFin.coeffSpan (ρ τ))
  refine ⟨(C ×ˢ Fintype.piFinset S).image fun p => p.1 * kInf θ V ε fr p.2, fun φ hφ h0 => ?_⟩
  funext g
  obtain ⟨n, hn, l, hl, c', hc, κ, u, hu, hu', rfl⟩ := hC g
  rw [hφ.2.1 u hu hu', mul_assoc (n * l), mul_assoc n, hφ.1.left n (Subgroup.mem_sup_left hn), ← mul_assoc]
  refine eq_zero_of_kInf hθ hfr hφ.2.2.1 S hS (l * c') (fun s hs => ?_) κ
  rw [mul_assoc]
  exact h0 _ (Finset.mem_image.2 ⟨(c', s), Finset.mem_product.2 ⟨hc, hs⟩, rfl⟩) l hl

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.Sep
