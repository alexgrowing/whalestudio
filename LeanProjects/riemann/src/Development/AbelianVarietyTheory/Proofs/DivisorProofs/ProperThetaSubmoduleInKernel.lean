import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLinePolynomialEquivarianceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ThetaKerMaxInf

section Local

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def mkA (a : InfiniteAdeleRing F) (b : FiniteAdeleRing (𝓞 F) F) : AF F := (a, b)

@[simp] theorem mkA_fst (a : InfiniteAdeleRing F) (b : FiniteAdeleRing (𝓞 F) F) : (mkA a b).1 = a := rfl

@[simp] theorem mkA_snd (a : InfiniteAdeleRing F) (b : FiniteAdeleRing (𝓞 F) F) : (mkA a b).2 = b := rfl

theorem tens_mem_schA_of_ne {f : SInf F κ} (hf : f ≠ 0) {r : (κ → AF F) → ℂ}
    (hr : ∀ x z, At (evI F) z → r (x + z) = r x) (hs : tens (evI F) f r ∈ schA F κ) (f' : SInf F κ) :
    tens (evI F) f' r ∈ schA F κ := by
  obtain ⟨y₀, hy₀⟩ : ∃ y, f y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (DFunLike.ext _ _ fun y => by rw [h y]; rfl)
  set e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let pt : (κ → FiniteAdeleRing (𝓞 F) F) → κ → AF F := fun y i => mkA (e.symm (y₀ i)) (y i)
  let L := LinearMap.funLeft ℂ ℂ pt
  have hL : schA F κ ≤ (SB (κ → FiniteAdeleRing (𝓞 F) F)).comap L := by
    refine Submodule.span_le.2 ?_
    rintro Φ ⟨f₀, g, hg, rfl⟩
    have : L (pureA F f₀ g) = f₀ y₀ • g := by
      funext y
      show f₀ (fun i => e (e.symm (y₀ i))) * g (fun i => y i) = f₀ y₀ * g y
      simp
    show L (pureA F f₀ g) ∈ SB _
    rw [this]
    exact Submodule.smul_mem _ _ hg
  have hLs : L (tens (evI F) f r) ∈ SB _ := hL hs
  refine Submodule.subset_span ⟨f', (f y₀)⁻¹ • L (tens (evI F) f r), Submodule.smul_mem _ _ hLs, ?_⟩
  funext x
  have hz : At (evI F) (fun i => mkA ((x i).1 - e.symm (y₀ i)) 0) := by
    intro u hu
    funext i
    have hu1 : u.1 = 0 := by
      have : e u.1 = 0 := hu
      simpa using this
    show mkA (u.1 * ((x i).1 - e.symm (y₀ i))) (u.2 * 0) = 0
    rw [hu1, zero_mul, mul_zero]
    rfl
  have hx : pt (fun i => (x i).2) + (fun i => mkA ((x i).1 - e.symm (y₀ i)) 0) = x := by
    funext i
    show mkA (e.symm (y₀ i) + ((x i).1 - e.symm (y₀ i))) ((x i).2 + 0) = x i
    rw [add_sub_cancel, add_zero]
    rfl
  have hrx : r x = r (pt fun i => (x i).2) := by
    have := hr (pt fun i => (x i).2) _ hz
    rw [hx] at this
    exact this
  have hev : (fun i => evI F (pt (fun i => (x i).2) i)) = y₀ := by
    funext i
    simp [pt, evI, e]
  simp only [tens, pureA, Pi.smul_apply, smul_eq_mul, L, LinearMap.funLeft_apply, Function.comp_def]
  rw [hev, hrx]
  simp only [evI]
  field_simp

theorem rest_of_sub {f g : SInf F κ} (hfg : f - g ≠ 0) {r : (κ → AF F) → ℂ} (hr : Rest (evI F) (⇑(f - g)) r) :
    Rest (evI F) f r ∧ Rest (evI F) g r :=
  ⟨⟨hr.1, tens_mem_schA_of_ne hfg hr.1 hr.2 f⟩, ⟨hr.1, tens_mem_schA_of_ne hfg hr.1 hr.2 g⟩⟩

theorem tens_sub (f g : SInf F κ) (r : (κ → AF F) → ℂ) :
    tens (evI F) (⇑(f - g)) r = tens (evI F) f r - tens (evI F) g r := by
  funext x
  simp [tens, sub_mul]

theorem actsD_sub (T : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) {f g f₁ g₁ : SInf F κ} (hfg : f - g ≠ 0)
    (hf : ActsD (evI F) (fun t => T t) f f₁) (hg : ActsD (evI F) (fun t => T t) g g₁) :
    ActsD (evI F) (fun t => T t) (⇑(f - g)) (⇑(f₁ - g₁)) := by
  intro r hr x
  obtain ⟨hrf, hrg⟩ := rest_of_sub hfg hr
  have h := (hf r hrf x).sub (hg r hrg x)
  rw [tens_sub, tens_sub]
  have e1 : (fun t => T t (tens (evI F) f r - tens (evI F) g r) x) =
      fun t => T t (tens (evI F) f r) x - T t (tens (evI F) g r) x := by
    funext t
    simp [map_sub]
  show HasDerivAt (fun t => T t (tens (evI F) f r - tens (evI F) g r) x) (tens (evI F) f₁ r x - tens (evI F) g₁ r x) 0
  rw [e1]
  exact h

theorem acts_sub (T : Module.End ℂ ((κ → AF F) → ℂ)) {f g f₁ g₁ : SInf F κ} (hfg : f - g ≠ 0)
    (hf : Acts (evI F) T f f₁) (hg : Acts (evI F) T g g₁) :
    Acts (evI F) T (⇑(f - g)) (⇑(f₁ - g₁)) := by
  intro r hr
  obtain ⟨hrf, hrg⟩ := rest_of_sub hfg hr
  rw [tens_sub, tens_sub, map_sub, hf r hrf, hg r hrg]

end Local

theorem det_ne_zero_of_isCartan {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) : M.det ≠ 0 := by
  intro h0
  obtain ⟨y, hy, hMy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hy' : star y ≠ 0 := by simpa using hy
  have := h.2.2 (star y) hy'
  rw [star_star, hMy, dotProduct_zero] at this
  simp at this

theorem det_ne_zero_of_triple {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') : G.V.J.det ≠ 0 ∧ G.W.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  constructor
  · have h1 := det_ne_zero_of_isCartan (h.geo.hV.cartan w)
    intro h0
    apply h1
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  · have h1 := det_ne_zero_of_isCartan (h.geo.hW.cartan w)
    intro h0
    apply h1
    rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero]

theorem chars_quot {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {B : Base F E} {a a' : ℕ} {X : Chars F E} (h : X.IsGood B a a') :
    ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (X.β / X.α) (a + a') ∧
      IsHecke F E (X.β / X.α) := by
  refine ⟨fun u => ?_, ?_, fun x => ?_⟩
  · rw [MonoidHom.div_apply, Circle.coe_div, h.resβ u, h.resα u]
    split_ifs
    · simp
    · have : ((-1 : ℂ) ^ a')⁻¹ = (-1) ^ a' := by rw [← inv_pow, inv_neg, inv_one]
      rw [div_eq_mul_inv, this, pow_add]
  · show Continuous fun x => X.β x / X.α x
    exact h.heckeβ.1.div' h.heckeα.1
  · rw [MonoidHom.div_apply, h.heckeβ.2, h.heckeα.2, div_one]

theorem le_ker_of_ne : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ P : Submodule ℂ (SInf F (Fin a × Fin (a + a'))),
    GlobalTheory.Published.ThetaSubInf G.M B.ψ B.emb om P → P ≠ G.M.Pol B.ψ B.emb → P ≤ LinearMap.ker R.p := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM P hP hne
  have hKr : GlobalTheory.Published.ThetaSubInf G.M B.ψ B.emb om (G.M.Pol B.ψ B.emb ⊓ LinearMap.ker R.p) := by
    first
      | exact GlobalTheory.T.matched_pair_theta_identity F E σ B a a' G X om om' R Rf hM
      | exact GlobalTheory.T.matched_pair_theta_identity hKP F E σ B a a' G X om om' R Rf hM
  obtain ⟨-, -, hstW, hstK⟩ := GlobalTheory.T.real_line_polynomial_equivariance hKP F E σ B a a' G X om om' hM.triple
  have hT := hM.triple

  have hKne : G.M.Pol B.ψ B.emb ⊓ LinearMap.ker R.p ≠ G.M.Pol B.ψ B.emb := by
    intro h
    have hn := hM.real.nontriv
    have h0 : (G.M.Pol B.ψ B.emb).map R.p = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨f, hf, rfl⟩
      rw [← h] at hf
      exact (Submodule.mem_bot ℂ).2 hf.2
    exact bot_ne_top (h0.symm.trans hM.real.quot.onto)

  obtain ⟨hdV, hdW⟩ := det_ne_zero_of_triple hT
  obtain ⟨hres, hhecke⟩ := chars_quot hT.chars
  have hHowe := (hKP.howeDualityReal F E σ hT.base.cm a (a + a') G.V G.W G.M B.ψ X.β (X.β / X.α) om hT.base.std
    hT.geo.hV.herm hdV hT.geo.hW.skew hdW hT.chars.resβ hres hT.chars.heckeβ hhecke hT.weil B.emb hT.geo.hV.cartan
    hT.geo.hW.cartan).2 P _ hP hKr hne hKne

  have hmem : ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ g ∈ P, ∀ f₁ g₁ : SInf F (Fin a × Fin (a + a')), g₁ ∈ P → R.p f = R.p g →
      f - g ≠ 0 → (f - g ∈ G.M.Pol B.ψ B.emb ⊓ LinearMap.ker R.p → f₁ - g₁ ∈ G.M.Pol B.ψ B.emb ⊓ LinearMap.ker R.p) →
      R.p f₁ ∈ P.map R.p := by
    intro f hf g hg f₁ g₁ hg₁ hpg _ himp
    have hk : f - g ∈ G.M.Pol B.ψ B.emb ⊓ LinearMap.ker R.p :=
      Submodule.mem_inf.2 ⟨Submodule.sub_mem _ hf (hP.1 hg), LinearMap.mem_ker.2 (by rw [map_sub, hpg, sub_self])⟩
    have h0 : R.p (f₁ - g₁) = 0 := (himp hk).2
    rw [map_sub, sub_eq_zero] at h0
    rw [h0]
    exact Submodule.mem_map_of_mem hg₁
  have hlie : ∀ γ ∈ Lines σ G.W, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + a')),
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → R.p f ∈ P.map R.p → R.p f₁ ∈ P.map R.p := by
    rintro γ hγ f hf f₁ hd ⟨g, hg, hpg⟩
    obtain ⟨g₁, -, hgd, huniq⟩ := hstW γ hγ g (hP.1 hg)
    have hg₁ : g₁ ∈ P := hP.2.2.2.1 γ hγ g hg g₁ hgd
    by_cases hfg : f - g = 0
    · obtain rfl : f = g := sub_eq_zero.mp hfg
      rw [huniq f₁ hd]
      exact Submodule.mem_map_of_mem hg₁
    · exact hmem f hf g hg f₁ g₁ hg₁ hpg.symm hfg fun hk =>
        hKr.2.2.2.1 γ hγ _ hk _ (actsD_sub (fun t => om (1, γ (Multiplicative.ofAdd t))) hfg hd hgd)
  have hcpt : ∀ k ∈ KInf σ G.W B.emb, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin a × Fin (a + a')),
      Acts (evI F) (om (1, k)) f f₁ → R.p f ∈ P.map R.p → R.p f₁ ∈ P.map R.p := by
    rintro k hk f hf f₁ hd ⟨g, hg, hpg⟩
    obtain ⟨g₁, -, hgd, huniq⟩ := hstK k hk g (hP.1 hg)
    have hg₁ : g₁ ∈ P := hP.2.2.2.2 k hk g hg g₁ hgd
    by_cases hfg : f - g = 0
    · obtain rfl : f = g := sub_eq_zero.mp hfg
      rw [huniq f₁ hd]
      exact Submodule.mem_map_of_mem hg₁
    · exact hmem f hf g hg f₁ g₁ hg₁ hpg.symm hfg fun hk' =>
        hKr.2.2.2.2 k hk _ hk' _ (acts_sub (om (1, k)) hfg hd hgd)
  rcases hM.real.irred (P.map R.p) hlie hcpt with h | h
  · intro x hx
    have : R.p x ∈ P.map R.p := Submodule.mem_map_of_mem hx
    rw [h] at this
    exact (Submodule.mem_bot ℂ).1 this
  · exfalso
    apply hHowe
    refine le_antisymm (sup_le hP.1 inf_le_left) fun f hf => ?_
    obtain ⟨g, hg, hpg⟩ : R.p f ∈ P.map R.p := h ▸ Submodule.mem_top
    have hfg : f = g + (f - g) := by abel
    rw [hfg]
    exact Submodule.add_mem_sup hg
      (Submodule.mem_inf.2 ⟨Submodule.sub_mem _ hf (hP.1 hg), LinearMap.mem_ker.2 (by rw [map_sub, hpg, sub_self])⟩)

end GlobalTheory.ThetaKerMaxInf
