import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialOfLocal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
open Filter Topology

noncomputable section

namespace GlobalTheory.UnitaryCutoff

section Mix

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

def mix (e : R) (A : Matrix ι ι R) : Matrix ι ι R := e • A + (1 - e) • (1 : Matrix ι ι R)

theorem mix_mul_mul {e : R} (he : e * e = e) (A C B : Matrix ι ι R) :
    mix e A * C * mix e B = e • (A * C * B) + (1 - e) • C := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h1, sub_zero]
  simp only [mix, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one,
    he, h1, h2, h3, zero_smul, add_zero, zero_add]

theorem mix_mul {e : R} (he : e * e = e) (A B : Matrix ι ι R) :
    mix e A * mix e B = e • (A * B) + (1 - e) • (1 : Matrix ι ι R) := by
  have := mix_mul_mul he A 1 B
  rwa [Matrix.mul_one, Matrix.mul_one] at this

theorem mix_transpose (e : R) (A : Matrix ι ι R) : (mix e A)ᵀ = mix e Aᵀ := by
  simp [mix, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one]

theorem mix_map {S : Type} [CommRing S] [Algebra S R] (c : R →ₐ[S] R) {e : R} (hc : c e = e) (A : Matrix ι ι R) :
    (mix e A).map c = mix e (A.map c) := by
  ext i j
  simp only [mix, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  split_ifs <;> simp [hc]

end Mix

section Adele

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tendsto_mix_fin {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (AE F E)) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 F)) =>
      mix (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)) M) atTop (𝓝 M) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have h := (GlobalTheory.LocalGlobalChar.tendsto_eps_tens ((M - 1) i j)).add_const ((1 : Matrix ι ι (AE F E)) i j)
  rw [Matrix.sub_apply, sub_add_cancel] at h
  refine h.congr fun S => ?_
  simp only [mix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end Adele

theorem exists_approx : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {ι : Type} [Fintype ι] [DecidableEq ι] (J₀ : Matrix ι ι (AE F E)) (g : UG (cA σ) J₀), ∃ q : Finset (HeightOneSpectrum (𝓞 F)) → UG (cA σ) J₀, (∀ S, ((q S).1.1 : Matrix ι ι (AE F E)) = algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) • (g.1.1 : Matrix ι ι (AE F E)) + (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)) • (1 : Matrix ι ι (AE F E))) ∧ Tendsto q atTop (𝓝 g) := by
  intro F E _ _ _ _ _ σ ι _ _ J₀ g
  let e : Finset (HeightOneSpectrum (𝓞 F)) → AE F E := fun S => algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)
  have he : ∀ S, e S * e S = e S := fun S => by
    simp only [e]; rw [← map_mul, GlobalTheory.LocalGlobalChar.eps_mul_self]
  have hc : ∀ S, cA σ (e S) = e S := fun S => (cA σ).commutes _
  have hg : (g.1.1)ᵀ * J₀ * (g.1.1).map (cA σ) = J₀ := g.2
  have hs : ∀ S, e S • (1 : Matrix ι ι (AE F E)) + (1 - e S) • 1 = 1 := fun S => by
    rw [← add_smul, add_sub_cancel, one_smul]
  let u : Finset (HeightOneSpectrum (𝓞 F)) → GL ι (AE F E) := fun S =>
    ⟨mix (e S) g.1.1, mix (e S) g.1.inv, by rw [mix_mul (he S), g.1.val_inv, hs],
      by rw [mix_mul (he S), g.1.inv_val, hs]⟩
  have hu : ∀ S, u S ∈ UG (cA σ) J₀ := fun S => by
    show (mix (e S) g.1.1)ᵀ * J₀ * (mix (e S) g.1.1).map (cA σ) = J₀
    rw [mix_transpose, mix_map (cA σ) (hc S), mix_mul_mul (he S), hg,
      ← add_smul, add_sub_cancel, one_smul]
  refine ⟨fun S => ⟨u S, hu S⟩, fun S => rfl, ?_⟩
  refine (Topology.IsEmbedding.subtypeVal.tendsto_nhds_iff).2 ?_
  refine (Units.isEmbedding_embedProduct.tendsto_nhds_iff).2 ?_
  refine Tendsto.prodMk_nhds (tendsto_mix_fin g.1.1) ?_
  exact (MulOpposite.continuous_op.tendsto _).comp (tendsto_mix_fin g.1.inv)

end GlobalTheory.UnitaryCutoff

end
