import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsApprox
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGensModNsmulOfFgNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModRepsCardLeStatement

open NumberField Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.UCls.IdxK

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem fv_mem {n : ℕ} {L : Set (Fin n → E)} {t : Fin n → E} (ht : t ∈ L) : fv F t ∈ hat F L :=
  AddSubgroup.subset_closure ⟨1, fun v => one_mem _, t, ht, rfl⟩

theorem fv_add {n : ℕ} (x y : Fin n → E) : fv F (x + y) = fv F x + fv F y := by
  funext i; simp [fv, TensorProduct.tmul_add]

theorem fv_nsmul {n : ℕ} (M : ℕ) (x : Fin n → E) : fv F (M • x) = M • fv F x := by
  funext i
  exact map_nsmul (TensorProduct.mk F (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) E 1) M (x i)

theorem smul_mem_hat {n : ℕ} {L : Set (Fin n → E)} (hL : ∀ o : 𝓞 E, ∀ x ∈ L, o • x ∈ L)
    {a : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F}
    (ha : ∀ v, a v ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v) (o : 𝓞 E)
    {z : Fin n → RA F E} (hz : z ∈ hat F L) : (a ⊗ₜ[F] (o : E)) • z ∈ hat F L := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a * b, fun v => ?_, o • x, hL o x hx, ?_⟩
    · exact mul_mem (ha v) (hb v)
    · funext i
      simp [Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

end GlobalTheory.UCls.IdxK

namespace GlobalTheory.UCls.IdxK

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem cong_of_gens {n M : ℕ} {L : Set (Fin n → E)} (hL : ∀ o : 𝓞 E, ∀ x ∈ L, o • x ∈ L)
    (e : Fin n → Fin n → E)
    (he : ∀ x ∈ L, ∃ o : Fin n → 𝓞 E, ∃ y ∈ L, x = ∑ i, o i • e i + M • y)
    (g s : Matrix (Fin n) (Fin n) (RA F E))
    (hg : ∀ x ∈ hat F L, g *ᵥ x ∈ hat F L) (hs : ∀ x ∈ hat F L, s *ᵥ x ∈ hat F L)
    (hgs : ∀ i, ∃ y ∈ hat F L, g *ᵥ fv F (e i) - s *ᵥ fv F (e i) = M • y) :
    ∀ x ∈ hat F L, ∃ y ∈ hat F L, g *ᵥ x - s *ᵥ x = M • y := by
  intro x hx
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    obtain ⟨o, y, hy, rfl⟩ := he x hx
    choose w hw hwe using hgs
    set u : Fin n → RA F E := fun i => a ⊗ₜ[F] y i with hu
    have huH : u ∈ hat F L := AddSubgroup.subset_closure ⟨a, ha, y, hy, rfl⟩
    have key : (fun i => a ⊗ₜ[F] (∑ j, o j • e j + M • y) i) =
        ∑ j, (a ⊗ₜ[F] (o j : E)) • fv F (e j) + M • u := by
      funext i
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, TensorProduct.tmul_add, TensorProduct.tmul_sum, hu]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_eq_mul, fv, Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.smul_def]
      · exact map_nsmul (TensorProduct.mk F (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) E a) M (y i)
    refine ⟨∑ j, (a ⊗ₜ[F] (o j : E)) • w j + (g *ᵥ u - s *ᵥ u),
      add_mem (sum_mem fun j _ => smul_mem_hat hL ha (o j) (hw j)) (sub_mem (hg u huH) (hs u huH)), ?_⟩
    rw [key, ← Matrix.sub_mulVec, Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.sub_mulVec,
      smul_add, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_smul, Matrix.sub_mulVec, hwe j, smul_comm]
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨y1, h1, e1⟩ := hx
    obtain ⟨y2, h2, e2⟩ := hy
    refine ⟨y1 + y2, add_mem h1 h2, ?_⟩
    rw [Matrix.mulVec_add, Matrix.mulVec_add, smul_add, ← e1, ← e2]
    abel
  | neg x _ hx =>
    obtain ⟨y1, h1, e1⟩ := hx
    refine ⟨-y1, neg_mem h1, ?_⟩
    rw [Matrix.mulVec_neg, Matrix.mulVec_neg, smul_neg, ← e1]
    abel

theorem isKM_inv_mul {n M : ℕ} {c : E ≃ₐ[F] E} {G : Matrix (Fin n) (Fin n) E} {L : Set (Fin n → E)}
    {g s : Matrix (Fin n) (Fin n) (RA F E)} (hg : IsKM c G L 1 g) (hs : IsKM c G L 1 s) (hsd : s.det = 1)
    (hgs : ∀ x ∈ hat F L, ∃ y ∈ hat F L, g *ᵥ x - s *ᵥ x = M • y) : IsKM c G L M (s⁻¹ * g) := by
  have hsu : IsUnit s.det := by rw [hsd]; exact isUnit_one
  have hss : ∀ v, s *ᵥ (s⁻¹ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hsu, Matrix.one_mulVec]
  have hss' : ∀ v, s⁻¹ *ᵥ (s *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hsu, Matrix.one_mulVec]
  have into : ∀ x ∈ hat F L, s *ᵥ x ∈ hat F L := by
    intro x hx
    obtain ⟨y, hy, h⟩ := hs.2.1 x hx
    rw [one_smul] at h
    rw [show s *ᵥ x = x + y by rw [← h]; abel]
    exact add_mem hx hy
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_nonsing_inv, hsd, Ring.inverse_one, one_mul]
    exact hg.1.1
  · intro x y
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hs.1.2 (s⁻¹ *ᵥ (g *ᵥ x)) (s⁻¹ *ᵥ (g *ᵥ y)), hss, hss,
      hg.1.2]
  · intro x hx
    obtain ⟨y, hy, h⟩ := hgs x hx
    obtain ⟨w, hw, rfl⟩ := hs.2.2 y hy
    refine ⟨w, hw, ?_⟩
    have h1 : g *ᵥ x = s *ᵥ (x + M • w) := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, ← h]; abel
    rw [← Matrix.mulVec_mulVec, h1, hss']
    abel
  · intro x hx
    obtain ⟨y, hy, h⟩ := hg.2.2 (s *ᵥ x) (into x hx)
    exact ⟨y, hy, by rw [← Matrix.mulVec_mulVec, h, hss']⟩

end GlobalTheory.UCls.IdxK

namespace GlobalTheory.UCls.IdxK

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem hat_approx {n M : ℕ} (hM : 1 ≤ M) {L : Set (Fin n → E)}
    (hL : ∀ b : 𝓞 F, ∀ x ∈ L, algebraMap F E (b : F) • x ∈ L) (hL0 : (0 : Fin n → E) ∈ L)
    (hLa : ∀ x ∈ L, ∀ y ∈ L, x + y ∈ L) (hLn : ∀ x ∈ L, -x ∈ L) :
    ∀ z ∈ hat F L, ∃ t ∈ L, ∃ y ∈ hat F L, z = fv F t + M • y := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    obtain ⟨b, y, hy, e⟩ := Formalism.UG.P.integral_adele_approximation_holds F (M : 𝓞 F) (by exact_mod_cast (by omega : M ≠ 0)) a ha
    refine ⟨algebraMap F E (b : F) • x, hL b x hx, fun i => y ⊗ₜ[F] x i,
      AddSubgroup.subset_closure ⟨y, hy, x, hx, rfl⟩, ?_⟩
    funext i
    rw [e]
    simp only [fv, Pi.add_apply, Pi.smul_apply, TensorProduct.add_tmul, smul_eq_mul]
    congr 1
    · rw [show algebraMap (𝓞 F) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) b =
          algebraMap F (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) (b : F) from rfl,
        Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def]
    · rw [map_natCast, ← nsmul_eq_mul, TensorProduct.smul_tmul']
  | zero => exact ⟨0, hL0, 0, zero_mem _, by funext i; simp [fv]⟩
  | add x y _ _ hx hy =>
    obtain ⟨t1, ht1, y1, hy1, rfl⟩ := hx
    obtain ⟨t2, ht2, y2, hy2, rfl⟩ := hy
    exact ⟨t1 + t2, hLa _ ht1 _ ht2, y1 + y2, add_mem hy1 hy2, by rw [fv_add, smul_add]; abel⟩
  | neg x _ hx =>
    obtain ⟨t1, ht1, y1, hy1, rfl⟩ := hx
    refine ⟨-t1, hLn _ ht1, -y1, neg_mem hy1, ?_⟩
    rw [neg_add, smul_neg]
    congr 1
    funext i; simp [fv, TensorProduct.tmul_neg]

end GlobalTheory.UCls.IdxK

namespace GlobalTheory.UCls.IdxK

theorem exists_reps_mod_KM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E)), 1 ≤ M → SelfDualLat G Λ →
    ∃ S : Finset (Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), S.card ≤ M ^ (2 * fdeg E * r ^ 2) ∧
      ∀ g, IsKM (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) 1 g → g.det = 1 →
        ∃ s ∈ S, IsKM (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) 1 s ∧ s.det = 1 ∧
          ∃ k, IsKM (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M k ∧ g = s * k := by
  intro E _ _ _ r M G Λ hM hSD
  classical
  have hFG : Λ.FG := hSD.2.2.1
  obtain ⟨e, heΛ, he⟩ := GlobalTheory.T.exists_gens_mod_nsmul_of_fg_numberField E r M Λ hM hFG
  obtain ⟨T, hTc, hTΛ, hT⟩ := GlobalTheory.T.exists_reps_mod_lattice_card_le E r M Λ hM hFG
  have hLo : ∀ o : 𝓞 E, ∀ x ∈ (Λ : Set (Fin r → E)), o • x ∈ (Λ : Set (Fin r → E)) :=
    fun o x hx => Λ.smul_mem o hx
  have hLb : ∀ b : 𝓞 (maximalRealSubfield E), ∀ x ∈ (Λ : Set (Fin r → E)),
      algebraMap (maximalRealSubfield E) E (b : maximalRealSubfield E) • x ∈ (Λ : Set (Fin r → E)) := by
    intro b x hx
    have hi : IsIntegral ℤ (algebraMap (maximalRealSubfield E) E (b : maximalRealSubfield E)) :=
      b.2.map (IsScalarTower.toAlgHom ℤ (maximalRealSubfield E) E)
    exact Λ.smul_mem (⟨_, hi⟩ : 𝓞 E) hx
  have hQ : ∀ z ∈ hat (maximalRealSubfield E) (Λ : Set (Fin r → E)), ∃ t ∈ T,
      ∃ y ∈ hat (maximalRealSubfield E) (Λ : Set (Fin r → E)), z = fv _ t + M • y := by
    intro z hz
    obtain ⟨t0, ht0, y0, hy0, rfl⟩ := hat_approx hM hLb Λ.zero_mem (fun x hx y hy => Λ.add_mem hx hy)
      (fun x hx => Λ.neg_mem hx) z hz
    obtain ⟨t, ht, y1, hy1, rfl⟩ := hT t0 ht0
    refine ⟨t, ht, fv _ y1 + y0, add_mem (fv_mem hy1) hy0, ?_⟩
    rw [fv_add, fv_nsmul, smul_add, add_assoc]
  have into : ∀ g, IsKM (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) 1 g →
      ∀ x ∈ hat (maximalRealSubfield E) (Λ : Set (Fin r → E)), g *ᵥ x ∈ hat (maximalRealSubfield E) (Λ : Set (Fin r → E)) := by
    intro g hg x hx
    obtain ⟨y, hy, h⟩ := hg.2.1 x hx
    rw [one_smul] at h
    rw [show g *ᵥ x = x + y by rw [← h]; abel]
    exact add_mem hx hy
  let K1 := {g : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E) //
    IsKM (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) 1 g ∧ g.det = 1}
  have hex : ∀ g : K1, ∀ i, ∃ t ∈ T, ∃ y ∈ hat (maximalRealSubfield E) (Λ : Set (Fin r → E)),
      g.1 *ᵥ fv _ (e i) = fv _ t + M • y :=
    fun g i => hQ _ (into g.1 g.2.1 _ (fv_mem (heΛ i)))
  choose τ hτT yy hyy hτ using hex
  let σ : (Fin r → Fin r → E) → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E) :=
    fun t => if h : ∃ g : K1, τ g = t then h.choose.1 else 1
  refine ⟨(Fintype.piFinset fun _ : Fin r => T).image σ, ?_, ?_⟩
  · calc _ ≤ (Fintype.piFinset fun _ : Fin r => T).card := Finset.card_image_le
      _ = T.card ^ r := by simp
      _ ≤ (M ^ (2 * fdeg E * r)) ^ r := Nat.pow_le_pow_left hTc r
      _ = _ := by rw [← pow_mul]; ring_nf
  · intro g hg hdet
    let g' : K1 := ⟨g, hg, hdet⟩
    have hex' : ∃ g'' : K1, τ g'' = τ g' := ⟨g', rfl⟩
    have hσ : σ (τ g') = hex'.choose.1 := dif_pos hex'
    have hsτ : τ hex'.choose = τ g' := hex'.choose_spec
    set s' := hex'.choose with hs'
    refine ⟨s'.1, Finset.mem_image.2 ⟨τ g', Fintype.mem_piFinset.2 fun i => hτT g' i, hσ⟩, s'.2.1, s'.2.2,
      s'.1⁻¹ * g, ?_, ?_⟩
    · refine isKM_inv_mul hg s'.2.1 s'.2.2 ?_
      refine cong_of_gens hLo e he g s'.1 (into g hg) (into s'.1 s'.2.1) fun i => ?_
      refine ⟨yy g' i - yy s' i, sub_mem (hyy g' i) (hyy s' i), ?_⟩
      have h1 := hτ g' i
      have h2 := hτ s' i
      rw [hsτ] at h2
      change g *ᵥ fv _ (e i) = _ at h1
      rw [h1, h2, smul_sub]
      abel
    · rw [← mul_assoc, Matrix.mul_nonsing_inv _ (by rw [s'.2.2]; exact isUnit_one), one_mul]

end GlobalTheory.UCls.IdxK
