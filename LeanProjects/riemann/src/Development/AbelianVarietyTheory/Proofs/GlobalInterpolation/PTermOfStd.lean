import Mathlib
import Formalism.LocalToGlobal.Columns.CoefColLemmas
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BelowFiniteNonempty
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SubstitutionAdjoint
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnitaryCarries

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.KerT

noncomputable section

namespace GlobalTheory.KerT.PAll

section Hom

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem mem_homAt_gmap (S : Finset (HeightOneSpectrum (𝓞 E))) (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b)
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (x : HomE E a b) :
    x ∈ homAt S (gmap g N) (gmap g' N') ↔ (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap : HomE E a b) ∈ homAt S N N' := by
  constructor
  · intro h P hP y hy
    have := h P hP (g y) ((mem_localization_gmap P g N _).2 (by simpa using hy))
    exact (mem_localization_gmap P g' N' _).1 this
  · intro h P hP y hy
    have := h P hP (g.symm y) ((mem_localization_gmap P g N _).1 hy)
    refine (mem_localization_gmap P g' N' _).2 ?_
    simpa using this

omit [NumberField E] [StarRing E] in
theorem conj_osmul (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) (c : 𝓞 E) (x : HomE E a b) :
    (g'.symm.toLinearMap ∘ₗ (c • x : HomE E a b) ∘ₗ g.toLinearMap : HomE E a b) =
      c • (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap : HomE E a b) := by
  rw [← algebraMap_smul E c x, ← algebraMap_smul E c, LinearMap.smul_comp, LinearMap.comp_smul]

theorem inBox_gmap {K : Type} [Field K] {S : Finset (HeightOneSpectrum (𝓞 E))} {cA cB : ℕ}
    {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)} {Ξ : HomE E a b → K}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.InBox S cA cB N N' Ξ) (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) :
    GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.InBox S cA cB (gmap g N) (gmap g' N') fun x => Ξ (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · have h1 : ((cA : 𝓞 E) • (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap : HomE E a b)) ∈ homAt S N N' := h.1 _ hx
    change ((cA : 𝓞 E) • x) ∈ homAt S (gmap g N) (gmap g' N')
    rwa [mem_homAt_gmap, conj_osmul]
  · obtain ⟨z, hz, rfl⟩ := hy
    have := h.2 (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) _ ⟨_, (mem_homAt_gmap S g g' N N' z).1 hz, rfl⟩
    refine Eq.trans ?_ this
    change Ξ (g'.symm.toLinearMap ∘ₗ (x + (cB : 𝓞 E) • z) ∘ₗ g.toLinearMap) =
      Ξ (_ + (cB : 𝓞 E) • (g'.symm.toLinearMap ∘ₗ z ∘ₗ g.toLinearMap : HomE E a b))
    rw [LinearMap.add_comp, LinearMap.comp_add, conj_osmul]

end Hom

variable {X : Fields} {n : ℕ}

theorem framed_gmap {SB : Finset (HeightOneSpectrum (𝓞 X.E))} {N : Submodule (𝓞 X.E) (Sp X.E n)} {fr : Frs X.E n SB}
    (h : Framed N fr) (g : Sp X.E n ≃ₗ[X.E] Sp X.E n) : Framed (gmap g N) fun P => g * fr P := by
  intro P x
  rw [mem_localization_gmap, ← h P x]
  simp

theorem rho_inv_apply (lam : X.Tau → DomWeight n) (γ : UF X.E n) (y : VV X.K lam) :
    rhoVr X.emb lam (ufGL X.E n γ⁻¹) (rhoVr X.emb lam (ufGL X.E n γ) y) = y := by
  rw [← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Module.End.one_apply]

theorem mem_localization_map {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module (𝓞 K) V] (w : HeightOneSpectrum (𝓞 K))
    (f : V →ₗ[𝓞 K] V) (hf : Function.Injective f) (M : Submodule (𝓞 K) V) (y : V) :
    f y ∈ localization₂ w.asIdeal (M.map f) ↔ y ∈ localization₂ w.asIdeal M := by
  rw [mem_locP, mem_locP]
  refine exists_congr fun s => and_congr_right fun _ => ?_
  rw [← map_smul]
  exact ⟨fun ⟨z, hz, h⟩ => hf h ▸ hz, fun h => ⟨_, h, rfl⟩⟩

theorem rho_mem_valAt (w : HeightOneSpectrum (𝓞 X.K)) (lam : X.Tau → DomWeight n) (γ : UF X.E n)
    (L : Submodule (𝓞 X.E) (Sp X.E n)) (y : VV X.K lam) :
    rhoVr X.emb lam (ufGL X.E n γ) y ∈ valAt w lam (gmap γ.1 L) ↔ y ∈ valAt w lam L := by
  unfold valAt
  rw [delAtr_gmap]
  exact mem_localization_map w ((rhoVr X.emb lam (ufGL X.E n γ)).restrictScalars (𝓞 X.K))
    (Function.LeftInverse.injective (rho_inv_apply lam γ)) _ y

theorem pTerm_of_std : ∀ (Z : Dat) (H : D7) (s : Seam H Z.X) (cc : Ideal (𝓞 H.host.K)) (δ : ℂ) (B : Base H cc δ) (χ : TaylorLogMetric.IdE H → ℂ) (cD : H.what₂.Tau → ℂ) (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)) (S : Set ℕ) (mu : Tup Z.X.F Z.X.E Z.X.K S) (cst : LocCst Z.X (rowSG Z.Pr sel mu)) (u : Z.Pr.Word) (i : ℕ), i < Z.R.m → Hyp Z s cc δ χ cD sel S mu cst u → RatTerm Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) → ∀ w : HeightOneSpectrum (𝓞 Z.X.K), (∀ {SG SG' : Finset (HeightOneSpectrum (𝓞 Z.X.E))} (d : DecoSet Z.X.E (Z.R.N i) (Z.Pr.vT u) SG) (fr : Frs Z.X.E (Z.R.N i) (rowSG Z.Pr sel mu)) (d' : DecoSet Z.X.E (Z.R.N (i + 1)) (Z.Pr.vT u) SG') (fr' : Frs Z.X.E (Z.R.N (i + 1)) (rowSG Z.Pr sel mu)) (Ξ₀ : HomE Z.X.E (Z.R.N i) (Z.R.N (i + 1)) → Z.X.K), StdOnly u i (i + 1) d d' → Framed d.1.N fr → Framed d'.1.N fr' → InBoxOfRowSelection sel mu cst u d.1.N d'.1.N Ξ₀ → (∀ x, w.valuation Z.X.K (Ξ₀ x) ≤ 1) → ∀ y ∈ valAt w (Z.W.lamTrue u i) d.1.Lsh, ((Z.Pr.T u : Z.X.K) ^ (((Z.X.f * Z.R.N i : ℕ) : ℤ) - ∑ τ, (Z.W.lamTrue u (i + 1) τ).detShift)) • term Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) d fr d' fr' Ξ₀ y ∈ valAt w (Z.W.lamTrue u (i + 1)) d'.1.L) → PTerm Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) w := by
  intro Z H s cc δ B χ cD sel S mu cst u i _ hyp hrat w hstd SG SG' d fr d' fr' Ξ₀ hfr hfr' hbox hint y hy
  obtain ⟨γ, hγ⟩ := GlobalTheory.StdReps.representatives Z.X hyp.ok.fields Z.Pr hyp.ok.primes u _ SG d
  obtain ⟨γ', hγ'⟩ := GlobalTheory.StdReps.representatives Z.X hyp.ok.fields Z.Pr hyp.ok.primes u _ SG' d'
  have e1 : (((γ, 1) : UF Z.X.E (Z.R.N i) × GLG Z.X.E (Z.R.N i) SG) • d).1.Lsh = gmap γ.1 d.1.Lsh :=
    Deco.Lsh_act d.1 γ.2 1
  have e2 : (((γ', 1) : UF Z.X.E (Z.R.N (i + 1)) × GLG Z.X.E (Z.R.N (i + 1)) SG') • d').1.L = gmap γ'.1 d'.1.L :=
    Deco.L_act d'.1 γ'.1 1
  have h := hstd _ (fun P => γ.1 * fr P) _ (fun P => γ'.1 * fr' P)
    (fun x => Ξ₀ (γ'.1.symm.toLinearMap ∘ₗ x ∘ₗ γ.1.toLinearMap)) ⟨fun P => hγ P.1 P.2, fun P => hγ' P.1 P.2⟩
    (framed_gmap hfr γ.1) (framed_gmap hfr' γ'.1) (inBox_gmap hbox γ.1 γ'.1) (fun _ => hint _)
    (rhoVr Z.X.emb _ (ufGL Z.X.E _ γ) y) (by rw [e1, rho_mem_valAt]; exact hy)
  rw [hrat d fr d' fr' Ξ₀ γ γ' hbox, e2, LinearMap.comp_apply, LinearMap.comp_apply, rho_inv_apply, ← map_smul,
    rho_mem_valAt] at h
  exact h

end GlobalTheory.KerT.PAll
