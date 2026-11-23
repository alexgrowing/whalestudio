import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSchwartzPairingSymmetric
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryPreservesPolynomialFock
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryPreservesPolynomialFockStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.DescB.FinKMatch

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
  {R : RealMaps F a a'} {Rf : FinMaps F a a'}

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have hA' : A'ᵀ * M * A'.map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]
    ext i j
    simp [A', Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.map_apply]
  have hD : (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)).det ≠ 0 := by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one]
    simp
  intro hM
  apply hD
  rw [← Matrix.det_submatrix_equiv_self e.symm, ← hA', Matrix.det_mul, Matrix.det_mul, hM, mul_zero, zero_mul]

theorem finite (hK : KP) (hM : IsMatched B G X om om' R Rf) (Φ : (Fin a × Fin (a + a') → AF F) → ℂ)
    (Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ) (hΦ' : Φ' ∈ G.M'.So B.ψ B.τ₁) (hPM : PolMatch B G X R Rf Φ Φ')
    (hf : UA σ G.W.J) (hhf : hf ∈ UAt σ G.W (fun u : AF F => u.2)) :
    om' (1, hf) Φ' ∈ G.M'.So B.ψ B.τ₁ ∧ PolMatch B G X R Rf (om (1, hf) Φ) (om' (1, hf) Φ') := by
  classical
  obtain ⟨h, hh⟩ := GlobalTheory.T.unitary_finite_adele_local_approximation F E σ _ G.W hf
  have hP := Inhab.pairV hM.triple
  have hP' := Inhab.pairV' hM.triple
  obtain ⟨S, hS⟩ := GlobalTheory.T.unitary_finite_local_approx_theta hK F E σ B _ _ G.V G.W G.M _ _ om _ _ _ _ hP hf hhf h hh
  obtain ⟨S', hS'⟩ := GlobalTheory.T.unitary_finite_local_approx_theta hK F E σ B _ _ G.V' G.W G.M' _ _ om' _ _ _ _ hP' hf hhf h hh
  constructor
  · refine Submodule.span_induction (p := fun x _ => om' (1, hf) x ∈ G.M'.So B.ψ B.τ₁) ?_ ?_ ?_ ?_ hΦ'
    · rintro _ ⟨f, φ, hφ, hcof, hv₁, rfl⟩
      have hfin := Filter.eventually_cofinite.1 hcof
      have hT0 : ∀ v ∉ hfin.toFinset ∪ S', φ v = G.M'.vac v := fun v hv => by
        by_contra hc
        exact hv (Finset.mem_union_left _ (hfin.mem_toFinset.2 hc))
      obtain ⟨φ₁, h1, h2, h3⟩ := hS' (hfin.toFinset ∪ S') Finset.subset_union_right f φ hφ hT0
      rw [h3]
      refine Submodule.subset_span ⟨f, φ₁, fun v => (h1 v).1, ?_, ?_, rfl⟩
      · refine Filter.eventually_cofinite.2 ((hfin.toFinset ∪ S').finite_toSet.subset fun v hv => ?_)
        by_contra hc
        exact hv (h2 v hc)
      · exact GlobalTheory.T.triple_local_action_at_special_place hK F E σ B a a' G X om om' hM.triple (h B.v₁) (hh B.v₁).1 (φ B.v₁) hv₁ (φ₁ B.v₁)
          (h1 B.v₁).1 (h1 B.v₁).2
    · rw [map_zero]; exact zero_mem _
    · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
    · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ c hx
  · obtain ⟨T, hXT, hOn⟩ := (PolynomialMatching.polMatch_iff B G X R Rf Φ Φ').1 hPM
    have hins : ∀ U : Finset (Pl F), PolynomialMatching.PolMatchOn B G X R Rf (T ∪ U) Φ Φ' := by
      intro U
      induction U using Finset.induction_on with
      | empty => simpa using hOn
      | insert v U _ ih =>
        by_cases hvX : v ∈ X.T
        · have e : T ∪ insert v U = T ∪ U := by
            ext w; simp only [Finset.mem_union, Finset.mem_insert]
            constructor
            · rintro (h | rfl | h)
              · exact Or.inl h
              · exact Or.inl (hXT hvX)
              · exact Or.inr h
            · rintro (h | h)
              · exact Or.inl h
              · exact Or.inr (Or.inr h)
          rw [e]; exact ih
        · have e : T ∪ insert v U = insert v (T ∪ U) := by
            ext w; simp only [Finset.mem_union, Finset.mem_insert]; tauto
          rw [e]
          exact PolynomialMatching.polMatchOn_insert F E σ B a a' G X R Rf v (hM.fin.sph v hvX).1 _ _ _ ih
    obtain ⟨m, m', f, φ, f', φ', hφ, hφ', rfl, rfl, hsum⟩ := hins (S ∪ S')
    have hTS : S ⊆ T ∪ (S ∪ S') := fun v hv => Finset.mem_union_right _ (Finset.mem_union_left _ hv)
    have hTS' : S' ⊆ T ∪ (S ∪ S') := fun v hv => Finset.mem_union_right _ (Finset.mem_union_right _ hv)
    choose φ₁ hφ₁ using fun i => hS (T ∪ (S ∪ S')) hTS (f i) (φ i) (hφ i).2.1 (hφ i).2.2
    choose φ₁' hφ₁' using fun j => hS' (T ∪ (S ∪ S')) hTS' (f' j) (φ' j) (hφ' j).2.1 (hφ' j).2.2
    have hL : ∀ v : Pl F, ∃ L : Rf.Pi v →ₗ[ℂ] Rf.Pi v,
        (∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₂ ∈ SB (Fin a × Fin (a + a') → Fv F v),
          Acts (evFin F v) (om (1, h v)) φ φ₂ → L (Rf.p v φ) = Rf.p v φ₂) ∧
        (∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₂ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
          Acts (evFin F v) (om' (1, h v)) φ φ₂ → L (Rf.p' v φ) = Rf.p' v φ₂) := by
      intro v
      have h1V : (1 : UA σ G.V.J) ∈ UAt σ G.V (evFin F v) := fun u _ => by
        show u • ((1 : UA σ G.V.J).1.1 - 1) = 0
        rw [show (1 : UA σ G.V.J).1.1 = 1 from rfl, sub_self, smul_zero]
      have hex : ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∃ φ₂ ∈ SB (Fin a × Fin (a + a') → Fv F v),
          Acts (evFin F v) (om (1, h v)) φ φ₂ :=
        fun φ hφ => LocalOps.acts_exists hP v (1, h v) h1V (hh v).1 φ hφ
      exact GlobalTheory.TrFin.transfer (SB _) (SB _) (Rf.p v) (Rf.p' v) _ _ (hM.fin.onto v) hex
        (fun φ hφ ψ hψ φ₂ ψ₂ h₁ h₂ c c' => LocalOps.acts_lin v _ hex hφ hψ h₁ h₂ c c')
        (GlobalTheory.TrFin.acts_zero v _)
        (fun φ hφ φ' hφ' φ₂ hφ₂ φ₂' hφ₂' => hM.fin.equiv v (h v) (hh v).1 φ hφ φ' hφ' φ₂ hφ₂ φ₂' hφ₂')
    choose L hL using hL
    refine ⟨T ∪ (S ∪ S'), fun v hv => Finset.mem_union_left _ (hXT hv), m, m', f, φ₁, f', φ₁', ?_, ?_, ?_, ?_, ?_⟩
    · intro i; exact ⟨(hφ i).1, fun v => ((hφ₁ i).1 v).1, (hφ₁ i).2.1⟩
    · intro j; exact ⟨(hφ' j).1, fun v => ((hφ₁' j).1 v).1, (hφ₁' j).2.1⟩
    · rw [map_sum]; exact Finset.sum_congr rfl fun i _ => (hφ₁ i).2.2
    · rw [map_sum]; exact Finset.sum_congr rfl fun j _ => (hφ₁' j).2.2
    · have key := congrArg (LinearMap.lTensor R.Pi
        (PiTensorProduct.map fun v : ↥(T ∪ (S ∪ S')) => L v.1)) hsum
      simp only [map_sum, LinearMap.lTensor_tmul, PiTensorProduct.map_tprod] at key
      have e1 : ∀ i, (fun v : ↥(T ∪ (S ∪ S')) => L v.1 (Rf.p v.1 (φ i v.1))) =
          fun v : ↥(T ∪ (S ∪ S')) => Rf.p v.1 (φ₁ i v.1) :=
        fun i => funext fun v => (hL v.1).1 _ ((hφ i).2.1 v) _ ((hφ₁ i).1 v).1 ((hφ₁ i).1 v).2
      have e2 : ∀ j, (fun v : ↥(T ∪ (S ∪ S')) => L v.1 (Rf.p' v.1 (φ' j v.1))) =
          fun v : ↥(T ∪ (S ∪ S')) => Rf.p' v.1 (φ₁' j v.1) :=
        fun j => funext fun v => (hL v.1).2 _ ((hφ' j).2.1 v) _ ((hφ₁' j).1 v).1 ((hφ₁' j).1 v).2
      simp only [e1, e2] at key
      exact key

theorem one_mem_UAt {n : ℕ} (Y : Spc F E n) {R' : Type} [Zero R'] (ev : AF F → R') : (1 : UA σ Y.J) ∈ UAt σ Y ev :=
  fun u _ => by
    show u • ((1 : UA σ Y.J).1.1 - 1) = 0
    rw [show (1 : UA σ Y.J).1.1 = 1 from rfl, sub_self, smul_zero]

theorem archimedean (hM : IsMatched B G X om om' R Rf) (Φ : (Fin a × Fin (a + a') → AF F) → ℂ)
    (Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ) (hΦ' : Φ' ∈ G.M'.So B.ψ B.τ₁) (hPM : PolMatch B G X R Rf Φ Φ')
    (k : UA σ G.W.J) (hk : k ∈ KInf σ G.W B.emb) :
    om' (1, k) Φ' ∈ G.M'.So B.ψ B.τ₁ ∧ PolMatch B G X R Rf (om (1, k) Φ) (om' (1, k) Φ') := by
  classical
  have hT := hM.triple
  have hP := Inhab.pairV hT
  have hP' := Inhab.pairV' hT
  obtain ⟨T, hT1⟩ := GlobalTheory.FockCompactW.exists_op_of_UAt hT.base.std hT.weil (1, k) (one_mem_UAt G.V _) hk.1
  obtain ⟨T', hT1'⟩ := GlobalTheory.FockCompactW.exists_op_of_UAt hT.base.std hT.weil' (1, k) (one_mem_UAt G.V' _) hk.1

  have hpure : ∀ (f : SInf F (Fin a × Fin (a + a'))) (φ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ),
      (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → om (1, k) (pure f φ) = pure (T f) φ := by
    intro f φ hSB hev
    have hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
      (hev.and hT.geo.hM.std).mono fun w hw => hw.1.trans hw.2
    exact hT1 f _ (GlobalTheory.ThK.EvUniqInf.rest_pure f φ hSB hstd)
  have hpure' : ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) → om' (1, k) (pure f φ) = pure (T' f) φ := by
    intro f φ hSB hev
    have hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
      (hev.and hT.geo.hM'.std).mono fun w hw => hw.1.trans hw.2
    exact hT1' f _ (GlobalTheory.ThK.EvUniqInf.rest_pure f φ hSB hstd)
  constructor
  · refine Submodule.span_induction (p := fun x _ => om' (1, k) x ∈ G.M'.So B.ψ B.τ₁) ?_ ?_ ?_ ?_ hΦ'
    · rintro _ ⟨f, φ, hφ, hcof, hv₁, rfl⟩
      rw [hpure' f φ hφ hcof]
      exact Submodule.subset_span ⟨T' f, φ, hφ, hcof, hv₁, rfl⟩
    · rw [map_zero]; exact zero_mem _
    · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
    · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ c hx
  · obtain ⟨w₀⟩ : Nonempty (F →+* ℂ) := inferInstance
    have hdet : ∀ {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (f : E →+* ℂ) (c : ℂ) (r s : ℕ), c ≠ 0 →
        HasSig (c • J.map f) r s → J.det ≠ 0 := by
      intro n J f c r s hc h hJ
      apply det_ne_zero_of_hasSig h
      rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hJ, map_zero, mul_zero]
    have hVd : G.V.J.det ≠ 0 := hdet G.V.J _ 1 _ _ one_ne_zero (by
      simpa using hP.herm.sig (InfinitePlace.mk w₀))
    have hV'd : G.V'.J.det ≠ 0 := hdet G.V'.J _ 1 _ _ one_ne_zero (by
      simpa using hP'.herm.sig (InfinitePlace.mk w₀))
    have hWd : G.W.J.det ≠ 0 := hdet G.W.J _ Complex.I _ _ Complex.I_ne_zero (hP.skew.sig (InfinitePlace.mk w₀))
    have hpol : ∀ f ∈ G.M.Pol B.ψ B.emb, T f ∈ G.M.Pol B.ψ B.emb := fun f hf =>
      (GlobalTheory.T.compactUnitary_preserves_polynomialFock F E σ hP.base.cm _ _ G.V G.W G.M B.ψ _ _ om hP.base.std hP.herm.herm hVd hP.skew.skew hWd
        hP.resX hP.resW hP.hX hP.hW hP.weil B.emb hP.herm.cartan hP.skew.cartan k hk f hf).2 (T f) (hT1 f)
    have hpol' : ∀ f ∈ G.M'.Pol B.ψ B.emb, T' f ∈ G.M'.Pol B.ψ B.emb := fun f hf =>
      (GlobalTheory.T.compactUnitary_preserves_polynomialFock F E σ hP'.base.cm _ _ G.V' G.W G.M' B.ψ _ _ om' hP'.base.std hP'.herm.herm hV'd hP'.skew.skew hWd
        hP'.resX hP'.resW hP'.hX hP'.hW hP'.weil B.emb hP'.herm.cartan hP'.skew.cartan k hk f hf).2 (T' f) (hT1' f)
    obtain ⟨L, hL, hL'⟩ := GlobalTheory.TrFin.transfer (G.M.Pol B.ψ B.emb) (G.M'.Pol B.ψ B.emb) R.p R.p'
      (fun f f₁ => f₁ = T f) (fun f f₁ => f₁ = T' f) hM.real.quot.onto (fun f hf => ⟨T f, hpol f hf, rfl⟩)
      (fun φ _ ψ _ φ₁ ψ₁ h₁ h₂ c c' => by
        show c • φ₁ + c' • ψ₁ = T (c • φ + c' • ψ)
        rw [h₁, h₂, map_add, map_smul, map_smul])
      (show (0 : SInf F (Fin a' × Fin (a + a'))) = T' 0 from (map_zero T').symm)
      (fun f hf f' hf' f₁ _ f₁' _ h₁ h₂ he => by
        subst h₁ h₂
        exact hM.real.cpt k hk f hf f' hf' (T f) (T' f') (hT1 f) (hT1' f') he)
    obtain ⟨S, hXS, m, m', f, φ, f', φ', hφ, hφ', rfl, rfl, hsum⟩ := hPM
    have hcof : ∀ (ψ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ), (∀ v ∉ S, ψ v = G.M.vac v) →
        ∀ᶠ v in cofinite, ψ v = G.M.vac v := fun ψ h =>
      Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => by by_contra hc; exact hv (h v hc))
    have hcof' : ∀ (ψ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ), (∀ v ∉ S, ψ v = G.M'.vac v) →
        ∀ᶠ v in cofinite, ψ v = G.M'.vac v := fun ψ h =>
      Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => by by_contra hc; exact hv (h v hc))
    refine ⟨S, hXS, m, m', fun i => T (f i), φ, fun j => T' (f' j), φ', ?_, ?_, ?_, ?_, ?_⟩
    · intro i; exact ⟨hpol _ (hφ i).1, (hφ i).2.1, (hφ i).2.2⟩
    · intro j; exact ⟨hpol' _ (hφ' j).1, (hφ' j).2.1, (hφ' j).2.2⟩
    · rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => hpure (f i) (φ i) (hφ i).2.1 (hcof _ (hφ i).2.2)
    · rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => hpure' (f' j) (φ' j) (hφ' j).2.1 (hcof' _ (hφ' j).2.2)
    · have key := congrArg (LinearMap.rTensor _ L) hsum
      simp only [map_sum, LinearMap.rTensor_tmul] at key
      have e1 : ∀ i, L (R.p (f i)) = R.p (T (f i)) := fun i => hL _ (hφ i).1 _ (hpol _ (hφ i).1) rfl
      have e2 : ∀ j, L (R.p' (f' j)) = R.p' (T' (f' j)) := fun j => hL' _ (hφ' j).1 _ (hpol' _ (hφ' j).1) rfl
      simp only [e1, e2] at key
      exact key

theorem translate_matched : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    GlobalTheory.ThK.KP → IsMatched B G X om om' R Rf → ∀ Φ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, PolMatch B G X R Rf Φ Φ' → ∀ k ∈ finK σ G.W B.emb,
      om' (1, k) Φ' ∈ G.M'.So B.ψ B.τ₁ ∧ PolMatch B G X R Rf (om (1, k) Φ) (om' (1, k) Φ') := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf hK hM Φ Φ' hΦ' hPM x hx
  obtain ⟨k, hk, g, hg, rfl⟩ := hx
  obtain ⟨h1, h2⟩ := finite hK hM Φ Φ' hΦ' hPM g hg
  have e : ∀ {n : ℕ} {Y : Spc F E n} (o : Rep σ Y G.W) (Ψ : (Fin n × Fin (a + a') → AF F) → ℂ),
      o (1, k * g) Ψ = o (1, k) (o (1, g) Ψ) := fun o Ψ => by
    rw [show ((1 : UA σ _), k * g) = (1, k) * (1, g) by simp, map_mul, Module.End.mul_apply]
  rw [e om, e om']
  exact archimedean hM _ _ h1 h2 k hk

end GlobalTheory.ThK.DescB.FinKMatch

end
