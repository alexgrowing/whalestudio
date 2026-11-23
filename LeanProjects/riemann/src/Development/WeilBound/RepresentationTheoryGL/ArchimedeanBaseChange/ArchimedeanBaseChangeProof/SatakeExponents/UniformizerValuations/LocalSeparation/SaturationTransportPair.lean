import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsNormalisedOfDualIsConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatGLOfInvT

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.RS

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open GlobalTheory.LFun.ConjPlace (dGL apply_heckeVec_shift Tj_shift_self satEig_inv_mul satEig_zero Tj_invT map_mem_Ov_iff
  mem_iff_invT dGL_comm)

namespace JetMatrixAlgebra

section Transport

variable {a b : ℕ}

omit [IsCMField E] in
theorem biInv_prod {P : Pl E} {p q : P.adicCompletion E} (hp : IsUnifV E P p) (hq : IsUnifV E P q) (i j : ℕ) :
    IsBiInv (K2 a b P) (fun g : GLw a P × GLw b P => Tj ℂ a (Ov E P) p i g.1 * Tj ℂ b (Ov E P) q j g.2) := by
  intro k1 k2 g
  obtain ⟨h11, h12⟩ := Subgroup.mem_prod.1 k1.2
  obtain ⟨h21, h22⟩ := Subgroup.mem_prod.1 k2.2
  simp only [Prod.fst_mul, Prod.snd_mul]
  rw [(Tj_mem_hecke hp i).1 ⟨_, h11⟩ ⟨_, h21⟩ g.1, (Tj_mem_hecke hq j).1 ⟨_, h12⟩ ⟨_, h22⟩ g.2]

omit [IsCMField E] in

theorem saturation_transport_pair {P P' : Pl E} {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GLw a P × GLw b P) V} {x : V} {Ba Bb : Multiset ℂˣ}
    (f : (GLw a P × GLw b P) ≃* (GLw a P' × GLw b P'))
    (hK : ∀ g, g ∈ K2 a b P ↔ f g ∈ K2 a b P') (hq : qV E P' = qV E P)
    (hT : ∀ ϖ', IsUnifV E P' ϖ' → ∃ ϖ : (P.adicCompletion E)ˣ, IsUnifV E P ϖ ∧ ∀ i ≤ a, ∀ j ≤ b, ∀ g,
      Tj ℂ a (Ov E P') ϖ' i (f g).1 * Tj ℂ b (Ov E P') ϖ' j (f g).2 =
        Tj ℂ a (Ov E P) ϖ (a - i) (dGL a ϖ a * g.1) * Tj ℂ b (Ov E P) ϖ (b - j) (dGL b ϖ b * g.2))
    (hx : IsSat2 P ρ x Ba Bb) : IsSat2 P' (ρ.comp f.symm.toMonoidHom) x (Ba.map (·⁻¹)) (Bb.map (·⁻¹)) := by
  obtain ⟨hf, ha, hb, hT0⟩ := hx
  refine ⟨(mem_fixed_comp_symm f hK).2 hf, by simpa using ha, by simpa using hb, fun ϖ' hϖ' i hi j hj => ?_⟩
  obtain ⟨ϖ, hp, hTT⟩ := hT ϖ' hϖ'
  let z : GLw a P × GLw b P := (dGL a ϖ a, dGL b ϖ b)
  have h1 := apply_heckeVec_shift (biInv_prod hp hp a b) hf z
  have e1 : (fun g : GLw a P × GLw b P => Tj ℂ a (Ov E P) (ϖ : P.adicCompletion E) a (z * g).1 *
      Tj ℂ b (Ov E P) (ϖ : P.adicCompletion E) b (z * g).2) =
      fun g => Tj ℂ a (Ov E P) (ϖ : P.adicCompletion E) 0 g.1 * Tj ℂ b (Ov E P) (ϖ : P.adicCompletion E) 0 g.2 :=
    funext fun g => by
      simp only [Prod.fst_mul, Prod.snd_mul, z]
      rw [Tj_shift_self, Tj_shift_self]
  rw [e1, hT0 _ hp 0 a.zero_le 0 b.zero_le, hT0 _ hp a le_rfl b le_rfl, satEig_zero, satEig_zero, one_mul,
    one_smul] at h1
  have h2 := apply_heckeVec_shift (biInv_prod hp hp (a - i) (b - j)) hf z
  rw [hT0 _ hp _ (a.sub_le i) _ (b.sub_le j), ← satEig_inv_mul ha hi, ← satEig_inv_mul hb hj,
    show satEig (qV E P) a (Ba.map (·⁻¹)) i * satEig (qV E P) a Ba a *
      (satEig (qV E P) b (Bb.map (·⁻¹)) j * satEig (qV E P) b Bb b) =
      (satEig (qV E P) a (Ba.map (·⁻¹)) i * satEig (qV E P) b (Bb.map (·⁻¹)) j) *
      (satEig (qV E P) a Ba a * satEig (qV E P) b Bb b) by ring, mul_smul, ← h1, ← map_smul] at h2
  rw [heckeVec_comp_symm f hK (biInv_prod hϖ' hϖ' i j) hf, hq]
  have e2 : ((fun g : GLw a P' × GLw b P' => Tj ℂ a (Ov E P') ϖ' i g.1 * Tj ℂ b (Ov E P') ϖ' j g.2) ∘ f) =
      fun g : GLw a P × GLw b P => Tj ℂ a (Ov E P) (ϖ : P.adicCompletion E) (a - i) (z * g).1 *
        Tj ℂ b (Ov E P) (ϖ : P.adicCompletion E) (b - j) (z * g).2 :=
    funext fun g => hTT i hi j hj g
  rw [e2]
  have h3 := congrArg (ρ z⁻¹) h2
  simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h3
  exact h3

end Transport

section Conj

open GlobalTheory.ThetaSatake

variable (x : Pl E) (n : ℕ)

def fx : GLw n x ≃* GLw n (cw x) :=
  (MulAut.conj (PhiU n (x.adicCompletion E))).symm.trans (GlobalTheory.LFun.ConjPlace.invT (cloc x).symm n)

theorem cloc_symm_v (y : x.adicCompletion E) : Valued.v ((cloc x).symm y) = Valued.v y := by
  have h := (conjLoc_spec (IsCMField.complexConj E).toRingEquiv x).2.2 ((cloc x).symm y)
  have e : conjLoc (IsCMField.complexConj E).toRingEquiv x ((cloc x).symm y) = y := (cloc x).apply_symm_apply y
  rw [e] at h
  exact h.symm

theorem mem_fx_iff (g : GLw n x) : g ∈ KGL x n ↔ fx x n g ∈ KGL (cw x) n := by
  have hO := map_mem_Ov_iff (cloc x).symm (cloc_symm_v x)
  have hΦ : PhiU n (x.adicCompletion E) ∈ KGL x n := phiU_mem _ n
  change _ ↔ GlobalTheory.LFun.ConjPlace.invT (cloc x).symm n ((MulAut.conj (PhiU n (x.adicCompletion E))).symm g) ∈ _
  rw [← mem_iff_invT (cloc x).symm hO, MulAut.conj_symm_apply, Subgroup.mul_mem_cancel_right _ hΦ,
    Subgroup.mul_mem_cancel_left _ (inv_mem hΦ)]

theorem Tj_fx {p : x.adicCompletion E} (hp : IsUnifV E x p) (hp0 : p ≠ 0) {j : ℕ} (hj : j ≤ n) (g : GLw n x) :
    Tj ℂ n (Ov E (cw x)) ((cloc x).symm p) j (fx x n g) =
      Tj ℂ n (Ov E x) ((Units.mk0 p hp0 : (x.adicCompletion E)ˣ) : x.adicCompletion E) (n - j)
        (dGL n (Units.mk0 p hp0) n * g) := by
  have hO := map_mem_Ov_iff (cloc x).symm (cloc_symm_v x)
  have hΦ : PhiU n (x.adicCompletion E) ∈ KGL x n := phiU_mem _ n
  change Tj ℂ n (Ov E (cw x)) ((cloc x).symm ((Units.mk0 p hp0 : (x.adicCompletion E)ˣ) : x.adicCompletion E)) j
    (GlobalTheory.LFun.ConjPlace.invT (cloc x).symm n ((MulAut.conj (PhiU n (x.adicCompletion E))).symm g)) = _
  rw [Tj_invT (cloc x).symm hO _ hj, MulAut.conj_symm_apply]
  have e : dGL n (Units.mk0 p hp0) n * ((PhiU n (x.adicCompletion E))⁻¹ * g * PhiU n (x.adicCompletion E)) =
      (PhiU n (x.adicCompletion E))⁻¹ * (dGL n (Units.mk0 p hp0) n * g) * PhiU n (x.adicCompletion E) := by
    rw [← mul_assoc (PhiU n (x.adicCompletion E))⁻¹, ← dGL_comm]; group
  rw [e]
  exact (Tj_mem_hecke (n := n) hp (n - j)).1 ⟨_, inv_mem hΦ⟩ ⟨_, hΦ⟩ _

theorem embT_cw (g : GLw n (cw x)) :
    embT n (cw x) g = embW n x (PhiU n (x.adicCompletion E) *
      GlobalTheory.LFun.ConjPlace.invT (cloc x) n g * (PhiU n (x.adicCompletion E))⁻¹) := by
  have h := GlobalTheory.ThetaPull.thetaA_finGL (E := E) (a := n) (locGL E n (cw x) g)
  rw [theta_locGL, thetaGL_conj] at h
  exact h

end Conj

open GlobalTheory.ThetaSatake in
theorem pairRtT_cw {a b : ℕ} (x : Pl E) :
    pairRtT a b (cw x) = (pairRt a b x).comp ((fx x a).prodCongr (fx x b)).symm.toMonoidHom := by
  ext1 g
  change rightReg ℂ (H E a b) ℂ (embT a (cw x) g.1, embT b (cw x) g.2) = rightReg ℂ (H E a b) ℂ (embW a x _, embW b x _)
  rw [embT_cw, embT_cw]
  rfl

end JetMatrixAlgebra

open JetMatrixAlgebra GlobalTheory.ThetaSatake in

theorem thetaSat2_holds : ThetaSat2 := by
  intro E _ _ _ a b w u G Ba Bb _ hwu hs
  obtain ⟨x, rfl⟩ : ∃ x, cw x = w := ⟨cw w, GlobalTheory.ThetaPull.conjSrc_conjSrc w⟩
  obtain rfl : u = x := (GlobalTheory.CompanionTheory.OneExDatum.eq_cw_of_conjPl hwu).trans (GlobalTheory.ThetaPull.conjSrc_conjSrc x)
  rw [pairRtT_cw]
  refine saturation_transport_pair _ (fun g => ?_) (absNorm_cw u) (fun ϖ' hϖ' => ?_) hs
  · show g ∈ (KGL u a).prod (KGL u b) ↔ ((fx u a).prodCongr (fx u b)) g ∈ (KGL (cw u) a).prod (KGL (cw u) b)
    rw [Subgroup.mem_prod, Subgroup.mem_prod]
    exact and_congr (mem_fx_iff u a g.1) (mem_fx_iff u b g.2)
  · obtain ⟨p, rfl⟩ := (cloc u).symm.surjective ϖ'
    have hp : IsUnifV E u p := (cloc_symm_v u p).symm.trans hϖ'
    have hp0 : p ≠ 0 := fun e => by simp [IsUnifV, e] at hp
    refine ⟨Units.mk0 p hp0, hp, fun i hi j hj g => ?_⟩
    exact congrArg₂ (· * ·) (Tj_fx u a hp hp0 hi g.1) (Tj_fx u b hp hp0 hj g.2)

end PositivityTheory.Rg.BcB.F.RS
