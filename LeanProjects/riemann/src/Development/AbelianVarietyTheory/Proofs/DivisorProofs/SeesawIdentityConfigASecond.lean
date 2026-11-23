import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorIsotropicTranslationCharSplitStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardResidueFieldOfRingEquivAdicCompletion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InsP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingEvaluationCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigATripleThetaLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFlipMatchSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitLocalSchwartzIntertwineStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EvZeroStd

theorem det_ne_of_hasSig' {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply]
  have h2 : (A'ᵀ * M * A'.map star).det ≠ 0 := by
    rw [h1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp [Matrix.det_neg]
  intro h0
  apply h2
  rw [Matrix.det_mul, Matrix.det_mul, h0]; simp

theorem det_ne_of_sig_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n r s : ℕ}
    (B : Base F E) (J : Matrix (Fin n) (Fin n) E) (c : ℂ) (h : ∀ w, HasSig (c • J.map (B.emb w).1) r s) : J.det ≠ 0 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have := det_ne_of_hasSig' (h w)
  intro h0; apply this
  have e := RingHom.map_det (B.emb w).1 J
  rw [RingHom.mapMatrix_apply] at e
  rw [Matrix.det_smul, ← e, h0, map_zero, mul_zero]

theorem mem_integer_iff' {F : Type} [Field F] [NumberField F] (v : Pl F) (a : Fv F v) :
    a ∈ 𝒪[Fv F v] ↔ a ∈ v.adicCompletionIntegers F := by
  rw [Valuation.mem_integer_iff, ← map_one (valuation (Fv F v)), ← Valuation.Compatible.vle_iff_le,
    HeightOneSpectrum.mem_adicCompletionIntegers,
    ← map_one (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))]
  exact Iff.rfl

theorem pairM_neg_right {k A C : Type} [CommRing k] [Fintype A] [Fintype C] (X Y : Matrix A C k) :
    GlobalTheory.FlipMatch.pairM X (-Y) = -GlobalTheory.FlipMatch.pairM X Y := by
  simp [GlobalTheory.FlipMatch.pairM, Finset.sum_neg_distrib]

theorem pairM_zero_right {k A C : Type} [CommRing k] [Fintype A] [Fintype C] (X : Matrix A C k) :
    GlobalTheory.FlipMatch.pairM X 0 = 0 := by
  simp [GlobalTheory.FlipMatch.pairM]

theorem pairM_zero_left {k A C : Type} [CommRing k] [Fintype A] [Fintype C] (X : Matrix A C k) :
    GlobalTheory.FlipMatch.pairM 0 X = 0 := by
  simp [GlobalTheory.FlipMatch.pairM]

theorem evZero_stdB : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ e' ei' ev', IsEv B G.M' G₁.M' 1 H'.ι (iso0 a' H') e' → IsLocPart G.M' G₁.M' e' ei' ev' → ∀ v : B.P, v.1 ∈ X.T →
    ∀ ι' ι₁', G.M'.IsLinBar B.ψ (B.τ v) (G.V'.bas v) (G.W.bas v) ι' → G₁.M'.IsLinBar B.ψ (B.τ v) (G₁.V'.bas v) (G₁.W.bas v) ι₁' →
      ι' (G.M'.vac v) = Set.indicator {Y | ∀ i j, Y i j ∈ v.1.adicCompletionIntegers F} 1 → ι₁' (G₁.M'.vac v) = Set.indicator {Y | ∀ i j, Y i j ∈ v.1.adicCompletionIntegers F} 1 →
      ∀ φ' ∈ SB (Fin a' × Fin (b + 2 + a') → Fv F v.1), ι' φ' = stdB (chrW X.ν (B.τ v)) (unifAt v.1) (condExp (chrW X.ν (B.τ v))) (b + 2) a' →
      ∀ φ₁' ∈ SB (Fin a' × Fin (b + a') → Fv F v.1), ι₁' φ₁' = stdB (chrW X.ν (B.τ v)) (unifAt v.1) (condExp (chrW X.ν (B.τ v))) b a' →
        ev' v φ' = ((Ideal.absNorm v.1.asIdeal : ℂ) ^ (-(((condExp (chrW X.ν (B.τ v))) * a' : ℕ) : ℤ))) • φ₁' := by
  intro _ F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' om₁ om₁' hT hT₁ e' ei' ev' hEv hLP v hv ι' ι₁' hι hι₁ hvac hvac₁
    φ' hφ' hφ'eq φ₁' hφ₁' hφ₁'eq
  have hcm := hT.base.cm
  have hstd := hT.base.std
  have hMg := hT.geo.hM'
  have hM₁g := hT₁.geo.hM'
  have dV' : G.V'.J.det ≠ 0 := det_ne_of_sig_smul B _ 1 (fun w => by rw [one_smul]; exact hT.geo.hV'.sig w)
  have dW : G.W.J.det ≠ 0 := det_ne_of_sig_smul B _ Complex.I hT.geo.hW.sig
  have dV₁' : G₁.V'.J.det ≠ 0 := det_ne_of_sig_smul B _ 1 (fun w => by rw [one_smul]; exact hT₁.geo.hV'.sig w)
  have dW₁ : G₁.W.J.det ≠ 0 := det_ne_of_sig_smul B _ Complex.I hT₁.geo.hW.sig
  obtain ⟨hinv, hheis⟩ := GlobalTheory.T.embedding_evaluation_compatible B G.M' G₁.M' 1 H'.ι (iso0 a' H') e' ei' ev' hMg hM₁g hEv hLP v.1
  obtain ⟨hco, hy⟩ := GlobalTheory.T.config_A_triple_theta_lift B b a' G G₁ H H' hC X om om' om₁ om₁' hT hT₁ v
  have act : ∀ {n d : ℕ} {Y : Spc F E n} {Z : Spc F E d} (M : Model σ Y Z) (u : Matrix (Fin n) (Fin d) (AE F E)),
      At (evFin F v.1) u → ∀ φ ∈ SB (Fin n × Fin d → Fv F v.1),
      ∃ φ₁ ∈ SB (Fin n × Fin d → Fv F v.1), Acts (evFin F v.1) (M.co.rho B.ψ u) φ φ₁ := by
    intro n d Y Z M u hu φ hφ
    have h := (locOp_rho M.co hstd.1 v.1 u hφ).1
    rw [partFin_of_at hu] at h
    exact ⟨_, locOp_mem _ _ _, h⟩
  have hbij := Model.IsLin.bij hι
  have hbij₁ := Model.IsLin.bij hι₁
  have hlinv : Set.LeftInvOn (Function.invFunOn ι' (SB (Fin a' × Fin (b + 2 + a') → Fv F v.1) : Set _)) ι'
      (SB (Fin a' × Fin (b + 2 + a') → Fv F v.1) : Set _) := hbij.injOn.leftInvOn_invFunOn
  set S : (Matrix (Fin a') (Fin (b + 2 + a')) (Fv F v.1) → ℂ) → Matrix (Fin a') (Fin (b + a')) (Fv F v.1) → ℂ :=
    fun f => ι₁' (ev' v.1 (Function.invFunOn ι' (SB (Fin a' × Fin (b + 2 + a') → Fv F v.1) : Set _) f)) with hSdef
  have hS : ∀ φ ∈ SB (Fin a' × Fin (b + 2 + a') → Fv F v.1), S (ι' φ) = ι₁' (ev' v.1 φ) := fun φ hφ => by
    rw [hSdef]; dsimp only; rw [hlinv hφ]
  have hevSB : ∀ φ ∈ SB (Fin a' × Fin (b + 2 + a') → Fv F v.1), ev' v.1 φ ∈ SB (Fin a' × Fin (b + a') → Fv F v.1) :=
    fun φ hφ => (hLP.2.1 v.1).2 ▸ Submodule.mem_map_of_mem hφ
  have hpsi0 : ∀ x : Fv F v.1, x = 0 → psiLoc B.ψ v.1 x = 1 := fun x hx => by
    rw [hx, ← GlobalTheory.LatVac.psiAt_apply, AddChar.map_zero_eq_one]
  have hlin : ∀ f ∈ SB (Matrix (Fin a') (Fin (b + 2 + a')) (Fv F v.1)), ∀ g ∈ SB (Matrix (Fin a') (Fin (b + 2 + a')) (Fv F v.1)),
      ∀ z : ℂ, S (z • f + g) = z • S f + S g := by
    intro f hf g hg z
    obtain ⟨φ, hφ, rfl⟩ := hbij.surjOn hf
    obtain ⟨χ, hχ, rfl⟩ := hbij.surjOn hg
    have hm : z • φ + χ ∈ SB (Fin a' × Fin (b + 2 + a') → Fv F v.1) := add_mem (Submodule.smul_mem _ z hφ) hχ
    rw [← map_smul, ← map_add, hS _ hm, hS _ hφ, hS _ hχ, map_add, map_smul, map_add, map_smul]
  have hT3 : ∀ f ∈ SB (Matrix (Fin a') (Fin (b + 2 + a')) (Fv F v.1)), ∀ r : Fin a' → Fv F v.1,
      S (fun Z => f (Z + Matrix.vecMulVec r (Pi.single ⟨b + 1, by omega⟩ 1))) = S f := by
    intro f hf r
    obtain ⟨φ, hφ, rfl⟩ := hbij.surjOn hf
    obtain ⟨y, hyat, hyX, hyY⟩ := hy 0 r
    obtain ⟨φ₁, hφ₁, hact⟩ := act G.M' _ hyat φ hφ
    have h62 := (GlobalTheory.T.heisenbergOperator_isotropic_translation_char_split hcm G.V' G.W hT.geo.hV'.herm hT.geo.hW.skew dV' dW G.M' B.ψ hstd (B.τ v) (G.V'.bas v)
      (G.W.bas v) _ hyat (by rw [hyX, Matrix.zero_vecMulVec, pairM_zero_left]) φ hφ φ₁ hφ₁ hact).2 ι' hι
    have e1 : (fun Z => ι' φ (Z + Matrix.vecMulVec r (Pi.single ⟨b + 1, by omega⟩ 1))) = ι' φ₁ := by
      funext Z
      rw [h62 Z, hyX, hyY, Matrix.zero_vecMulVec, pairM_zero_right, hpsi0 _ neg_zero, one_mul]
    rw [e1, hS _ hφ₁, hS _ hφ, hinv _ ⟨y, rfl⟩ φ hφ φ₁ hφ₁ hact]
  have hT4 : ∀ f ∈ SB (Matrix (Fin a') (Fin (b + 2 + a')) (Fv F v.1)), ∀ s : Fin a' → Fv F v.1,
      S (fun Z => GlobalTheory.LatVac.psiAt B.ψ v.1 (GlobalTheory.FlipMatch.pairM Z (Matrix.vecMulVec s (Pi.single 0 1))) * f Z) = S f := by
    intro f hf s
    obtain ⟨φ, hφ, rfl⟩ := hbij.surjOn hf
    obtain ⟨y, hyat, hyX, hyY⟩ := hy (-s) 0
    obtain ⟨φ₁, hφ₁, hact⟩ := act G.M' _ hyat φ hφ
    have h62 := (GlobalTheory.T.heisenbergOperator_isotropic_translation_char_split hcm G.V' G.W hT.geo.hV'.herm hT.geo.hW.skew dV' dW G.M' B.ψ hstd (B.τ v) (G.V'.bas v)
      (G.W.bas v) _ hyat (by rw [hyY, Matrix.zero_vecMulVec, pairM_zero_right]) φ hφ φ₁ hφ₁ hact).2 ι' hι
    have e1 : (fun Z => GlobalTheory.LatVac.psiAt B.ψ v.1 (GlobalTheory.FlipMatch.pairM Z (Matrix.vecMulVec s (Pi.single 0 1))) * ι' φ Z) =
        ι' φ₁ := by
      funext Z
      rw [h62 Z, hyX, hyY, Matrix.zero_vecMulVec, add_zero, Matrix.neg_vecMulVec, pairM_neg_right, neg_neg,
        GlobalTheory.LatVac.psiAt_apply]
    rw [e1, hS _ hφ₁, hS _ hφ, hinv _ ⟨y, rfl⟩ φ hφ φ₁ hφ₁ hact]
  have hAt : ∀ z : Matrix (Fin a') (Fin (b + a')) (AE F E), At (evFin F v.1) z →
      At (evFin F v.1) (incM F (1 : Matrix (Fin a') (Fin a') E) * z * (incM F H'.ι)ᵀ) := by
    intro z hz a ha
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hz a ha, Matrix.mul_zero, Matrix.zero_mul]
  have hT1 : ∀ f ∈ SB (Matrix (Fin a') (Fin (b + 2 + a')) (Fv F v.1)), ∀ Y : Matrix (Fin a') (Fin (b + a')) (Fv F v.1),
      S (fun Z => f (Z + Y * (insP (Fv F v.1) b a')ᵀ)) = fun Z => S f (Z + Y) := by
    intro f hf Y
    obtain ⟨φ, hφ, rfl⟩ := hbij.surjOn hf
    obtain ⟨z, hzat, hzX, hzY⟩ := GlobalTheory.T.local_flip_match_surjective hcm G₁.V' G₁.W dV₁' dW₁ (B.τ v) (G₁.V'.bas v) (G₁.W.bas v) 0 Y
    have hu := hAt z hzat
    obtain ⟨φ₁, hφ₁, hact⟩ := act G.M' _ hu φ hφ
    obtain ⟨χ₁, hχ₁, hactχ⟩ := act G₁.M' z hzat (ev' v.1 φ) (hevSB φ hφ)
    have hX0 := (hco z).1
    have hY0 := (hco z).2
    rw [hzX, Matrix.zero_mul] at hX0
    rw [hzY] at hY0
    have h62 := (GlobalTheory.T.heisenbergOperator_isotropic_translation_char_split hcm G.V' G.W hT.geo.hV'.herm hT.geo.hW.skew dV' dW G.M' B.ψ hstd (B.τ v) (G.V'.bas v)
      (G.W.bas v) _ hu (by rw [hX0, pairM_zero_left]) φ hφ φ₁ hφ₁ hact).2 ι' hι
    have h62' := (GlobalTheory.T.heisenbergOperator_isotropic_translation_char_split hcm G₁.V' G₁.W hT₁.geo.hV'.herm hT₁.geo.hW.skew dV₁' dW₁ G₁.M' B.ψ hstd (B.τ v)
      (G₁.V'.bas v) (G₁.W.bas v) z hzat (by rw [hzX, pairM_zero_left]) (ev' v.1 φ) (hevSB φ hφ) χ₁ hχ₁ hactχ).2 ι₁' hι₁
    have e1 : (fun Z => ι' φ (Z + Y * (insP (Fv F v.1) b a')ᵀ)) = ι' φ₁ := by
      funext Z
      rw [h62 Z, hX0, hY0, pairM_zero_right, hpsi0 _ neg_zero, one_mul]
    rw [e1, hS _ hφ₁, hS _ hφ, hheis z φ hφ φ₁ hφ₁ hact χ₁ hχ₁ hactχ]
    funext Z
    rw [h62' Z, hzX, hzY, pairM_zero_right, hpsi0 _ neg_zero, one_mul]
  have hT2 : ∀ f ∈ SB (Matrix (Fin a') (Fin (b + 2 + a')) (Fv F v.1)), ∀ Y : Matrix (Fin a') (Fin (b + a')) (Fv F v.1),
      S (fun Z => GlobalTheory.LatVac.psiAt B.ψ v.1 (GlobalTheory.FlipMatch.pairM Z (Y * (insP (Fv F v.1) b a')ᵀ)) * f Z) =
        fun Z => GlobalTheory.LatVac.psiAt B.ψ v.1 (GlobalTheory.FlipMatch.pairM Z Y) * S f Z := by
    intro f hf Y
    obtain ⟨φ, hφ, rfl⟩ := hbij.surjOn hf
    obtain ⟨z, hzat, hzX, hzY⟩ := GlobalTheory.T.local_flip_match_surjective hcm G₁.V' G₁.W dV₁' dW₁ (B.τ v) (G₁.V'.bas v) (G₁.W.bas v) (-Y) 0
    have hu := hAt z hzat
    obtain ⟨φ₁, hφ₁, hact⟩ := act G.M' _ hu φ hφ
    obtain ⟨χ₁, hχ₁, hactχ⟩ := act G₁.M' z hzat (ev' v.1 φ) (hevSB φ hφ)
    have hX0 := (hco z).1
    have hY0 := (hco z).2
    rw [hzX] at hX0
    rw [hzY, Matrix.zero_mul] at hY0
    have h62 := (GlobalTheory.T.heisenbergOperator_isotropic_translation_char_split hcm G.V' G.W hT.geo.hV'.herm hT.geo.hW.skew dV' dW G.M' B.ψ hstd (B.τ v) (G.V'.bas v)
      (G.W.bas v) _ hu (by rw [hY0, pairM_zero_right]) φ hφ φ₁ hφ₁ hact).2 ι' hι
    have h62' := (GlobalTheory.T.heisenbergOperator_isotropic_translation_char_split hcm G₁.V' G₁.W hT₁.geo.hV'.herm hT₁.geo.hW.skew dV₁' dW₁ G₁.M' B.ψ hstd (B.τ v)
      (G₁.V'.bas v) (G₁.W.bas v) z hzat (by rw [hzY, pairM_zero_right]) (ev' v.1 φ) (hevSB φ hφ) χ₁ hχ₁ hactχ).2 ι₁' hι₁
    have e1 : (fun Z => GlobalTheory.LatVac.psiAt B.ψ v.1 (GlobalTheory.FlipMatch.pairM Z (Y * (insP (Fv F v.1) b a')ᵀ)) * ι' φ Z) = ι' φ₁ := by
      funext Z
      rw [h62 Z, hX0, hY0, add_zero, Matrix.neg_mul, pairM_neg_right, neg_neg, GlobalTheory.LatVac.psiAt_apply]
    rw [e1, hS _ hφ₁, hS _ hφ, hheis z φ hφ φ₁ hφ₁ hact χ₁ hχ₁ hactχ]
    funext Z
    rw [h62' Z, hzX, hzY, add_zero, pairM_neg_right, neg_neg, GlobalTheory.LatVac.psiAt_apply]
  have hset : ∀ (p q : ℕ), {Z : Matrix (Fin p) (Fin q) (Fv F v.1) | ∀ i j, Z i j ∈ 𝒪[Fv F v.1]} =
      {Y | ∀ i j, Y i j ∈ v.1.adicCompletionIntegers F} := fun p q => by
    ext Z; simp only [Set.mem_setOf_eq, mem_integer_iff']
  have hvacS : S (Set.indicator {Z | ∀ i j, Z i j ∈ 𝒪[Fv F v.1]} 1) = Set.indicator {Z | ∀ i j, Z i j ∈ 𝒪[Fv F v.1]} 1 := by
    rw [hset, hset, ← hvac, ← hvac₁, hS _ (hMg.vac v.1).1, (hLP.2.1 v.1).1]
  have hψ : ∀ x : Fv F v.1, (∀ y ∈ 𝒪[Fv F v.1], GlobalTheory.LatVac.psiAt B.ψ v.1 (x * y) = 1) ↔ x ∈ 𝒪[Fv F v.1] := by
    intro x
    simpa only [mem_integer_iff', GlobalTheory.LatVac.psiAt_apply] using hT.base.psiP v.1 v.2 x
  have hϖ : GlobalTheory.SplitFlip.IsUnif (unifAt v.1) := GlobalTheory.SplitFlip.exists_isUnif.choose_spec
  have key := GlobalTheory.T.split_local_schwartz_intertwine (Fv F v.1) (GlobalTheory.LatVac.psiAt B.ψ v.1) hψ (chrW X.ν (B.τ v)) (unifAt v.1) hϖ (condExp (chrW X.ν (B.τ v)))
    b a' S hlin hT3 hT4 hT1 hT2 hvacS (hφ'eq ▸ hbij.mapsTo hφ')
  have hq : Nat.card 𝓀[Fv F v.1] = Ideal.absNorm v.1.asIdeal :=
    GlobalTheory.LocalResidue.card_residue_of_ringEquiv F v.1 (Fv F v.1) (RingEquiv.refl _) fun a => by
      rw [mem_integer_iff', HeightOneSpectrum.mem_adicCompletionIntegers]; rfl
  have hsm : ((Ideal.absNorm v.1.asIdeal : ℂ) ^ (-(((condExp (chrW X.ν (B.τ v))) * a' : ℕ) : ℤ))) • φ₁' ∈
      SB (Fin a' × Fin (b + a') → Fv F v.1) := Submodule.smul_mem _ _ hφ₁'
  refine hbij₁.injOn (hevSB φ' hφ') hsm ?_
  rw [← hS _ hφ', hφ'eq, key, hq, map_smul, hφ₁'eq]

end GlobalTheory.EvZeroStd
