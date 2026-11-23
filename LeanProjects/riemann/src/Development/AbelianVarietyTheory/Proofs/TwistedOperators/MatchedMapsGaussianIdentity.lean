import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalAtFinitePlaceUnitaryGroupStatement

open NumberField IsDedekindDomain
open scoped Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.HoweNonsplitKerSmall

theorem det_ne_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
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

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem det_ne_of_sig {n r s : ℕ} (B : Base F E) (J : Matrix (Fin n) (Fin n) E) (c : ℂ)
    (h : ∀ w, HasSig (c • J.map (B.emb w).1) r s) : J.det ≠ 0 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have := det_ne_of_hasSig (h w)
  intro h0; apply this
  have e := RingHom.map_det (B.emb w).1 J
  rw [RingHom.mapMatrix_apply] at e
  rw [Matrix.det_smul, ← e, h0, map_zero, mul_zero]

theorem isHecke_div {χ₁ χ₂ : Chr F E} (h₁ : IsHecke F E χ₁) (h₂ : IsHecke F E χ₂) : IsHecke F E (χ₁ / χ₂) := by
  refine ⟨?_, fun x => ?_⟩
  · show Continuous fun x => χ₁ x / χ₂ x
    exact h₁.1.div' h₂.1
  · rw [MonoidHom.div_apply, h₁.2 x, h₂.2 x, div_one]

theorem resEtaPow_div {K : Subgroup (AF F)ˣ} {χ₁ χ₂ : Chr F E} {n₁ n₂ n : ℕ} (h₁ : ResEtaPow K χ₁ n₁)
    (h₂ : ResEtaPow K χ₂ n₂) (he : Even (n₁ + n₂)) (hn : Even n) : ResEtaPow K (χ₁ / χ₂) n := by
  intro x
  have e₁ := h₁ x
  have e₂ := h₂ x
  rw [MonoidHom.div_apply, Circle.coe_div, e₁, e₂, hn.neg_one_pow]
  split_ifs
  · simp
  · rcases Nat.even_or_odd n₁ with h | h
    · have h' : Even n₂ := (Nat.even_add.mp he).mp h
      rw [h.neg_one_pow, h'.neg_one_pow]; simp
    · have h' : Odd n₂ := by
        rcases Nat.even_or_odd n₂ with h'' | h''
        · exact absurd ((Nat.even_add.mp he).mpr h'') (Nat.not_even_iff_odd.mpr h)
        · exact h''
      rw [h.neg_one_pow, h'.neg_one_pow]; simp

theorem isPair_second {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
    GlobalTheory.ThK.IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, isHecke_div h.chars.heckeα h.chars.heckeβ, h.chars.resα,
    resEtaPow_div h.chars.resα h.chars.resβ (by rw [add_comm]; exact h.geo.even) h.geo.even, h.weil'⟩

theorem howe_nonsplit_ker_small : GlobalTheory.Published.HoweDualityFinite →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, IsEmpty (E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) →
      (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ((Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSub om' v (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ), GlobalTheory.Published.ThetaSub om' v N →
        N ≠ GlobalTheory.WeilM.SB _ → ∀ φ ∈ N, Rf.p' v φ = 0 := by
  intro hHD F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM v hv
  have hT := hM.triple
  have P := isPair_second hT
  obtain ⟨hbdd, hsum⟩ := hHD F E σ P.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' P.base.std
    P.herm.herm (det_ne_of_sig Bs G.V'.J 1 (fun w => by rw [one_smul]; exact P.herm.sig w)) P.skew.skew
    (det_ne_of_sig Bs G.W.J _ P.skew.sig) P.resX P.resW P.hX P.hW P.weil v hv
  refine ⟨hbdd, ?_⟩
  intro N hN hNe φ hφ
  have hex : ∀ h ∈ UAt σ G.W (evFin F v), ∀ ψ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∃ ψ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, h)) ψ ψ₁ :=
    GlobalTheory.T.weilRepresentation_localAtFinitePlace_unitaryGroupW F E σ Bs a a' G Xc om om' hT v
  set K : Submodule ℂ ((Fin a' × Fin (a + a') → Fv F v) → ℂ) :=
    LinearMap.ker (Rf.p' v) ⊓ SB (Fin a' × Fin (a + a') → Fv F v) with hKdef
  have haugSB : augAt om' v ≤ SB (Fin a' × Fin (a + a') → Fv F v) := by
    refine Submodule.span_le.2 ?_
    rintro z ⟨g, -, ψ, hψ, ψ₁, hψ₁, -, rfl⟩
    exact sub_mem hψ₁ hψ
  have hK : GlobalTheory.Published.ThetaSub om' v K := by
    refine ⟨le_inf (hM.fin.inv' v) haugSB, inf_le_right, ?_⟩
    intro h hh ψ hψ ψ₁ hψ₁ hact
    have hψ' := Submodule.mem_inf.1 hψ
    have h0 : Acts (evFin F v) (om (1, h)) (0 : (Fin a × Fin (a + a') → Fv F v) → ℂ) 0 := by
      intro r _
      have e : tens (evFin F v) (0 : (Fin a × Fin (a + a') → Fv F v) → ℂ) r = 0 := by
        funext x; simp [tens]
      rw [e, map_zero]
    have hp := hM.fin.equiv v h hh 0 (zero_mem _) ψ hψ'.2 0 (zero_mem _) ψ₁ hψ₁ h0 hact
      (by rw [map_zero]; exact (LinearMap.mem_ker.1 hψ'.1).symm)
    rw [map_zero] at hp
    exact Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 hp.symm, hψ₁⟩
  have hKne : K ≠ SB (Fin a' × Fin (a + a') → Fv F v) := by
    intro hKe
    have hbot : (SB (Fin a' × Fin (a + a') → Fv F v)).map (Rf.p' v) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro _ ⟨ψ, hψ, rfl⟩
      rw [← hKe] at hψ
      exact LinearMap.mem_ker.1 (Submodule.mem_inf.1 hψ).1
    rw [hM.fin.onto' v] at hbot
    haveI := hM.fin.nontriv v
    exact top_ne_bot hbot
  have hNK : N ⊔ K ≠ SB (Fin a' × Fin (a + a') → Fv F v) := hsum N K hN hK hNe hKne
  rcases hM.fin.irred v (N.map (Rf.p' v)) (by
    intro h hh ψ hψ ψ₁ hψ₁ hact hpm
    obtain ⟨n, hn, hpn⟩ := Submodule.mem_map.1 hpm
    have hnSB : n ∈ SB (Fin a' × Fin (a + a') → Fv F v) := hN.2.1 hn
    obtain ⟨n₁, hn₁, hactn⟩ := hex h hh n hnSB
    have hn₁N : n₁ ∈ N := hN.2.2 h hh n hn n₁ hn₁ hactn
    rw [hM.fin.equiv v h hh ψ hψ n hnSB ψ₁ hψ₁ n₁ hn₁ hact hactn hpn.symm]
    exact Submodule.mem_map_of_mem hn₁N) with h0 | htop
  · have hmem : Rf.p' v φ ∈ N.map (Rf.p' v) := Submodule.mem_map_of_mem hφ
    rw [h0] at hmem
    exact (Submodule.mem_bot ℂ).1 hmem
  · exfalso
    apply hNK
    refine le_antisymm (sup_le hN.2.1 inf_le_right) ?_
    intro ψ hψ
    have hm : Rf.p' v ψ ∈ N.map (Rf.p' v) := by rw [htop]; exact Submodule.mem_top
    obtain ⟨n, hn, hpn⟩ := Submodule.mem_map.1 hm
    have hk : ψ - n ∈ K :=
      Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (by rw [map_sub, hpn, sub_self]), sub_mem hψ (hN.2.1 hn)⟩
    have := Submodule.add_mem_sup hn hk
    rwa [add_sub_cancel] at this

end GlobalTheory.HoweNonsplitKerSmall

end
