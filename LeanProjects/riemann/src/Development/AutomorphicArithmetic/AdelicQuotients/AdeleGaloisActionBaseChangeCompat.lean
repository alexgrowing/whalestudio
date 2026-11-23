import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open NumberField IsDedekindDomain GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open scoped NumberField.AdeleRing TensorProduct

open PositivityTheory.Rg.Tf.Loc

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem galOf_tmul' {A B : Type*} [CommRing A] [Algebra F A] [CommRing B] [Algebra E B]
    (e : E ⊗[F] A ≃ₐ[E] B) (σ : E ≃ₐ[F] E) (l : E) (a : A) :
    galOf e σ (e (l ⊗ₜ a)) = e (σ l ⊗ₜ a) := by
  simp [galOf]

private theorem tensor_fst (l : E) (x : 𝔸[F]) :
    (adeleTensorEquiv F E (l ⊗ₜ x)).1 =
      GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv (K := F) (L := E) (l ⊗ₜ x.1) := by
  rw [adeleTensorEquiv_tmul, GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_tmul']
  rfl

private theorem tensor_atFin (v : HeightOneSpectrum (𝓞 F)) (l : E) (x : 𝔸[F]) :
    atFin v (adeleTensorEquiv F E (l ⊗ₜ x)) = tensorEquiv' E v (l ⊗ₜ x.2 v) := by
  funext ⟨w, hw⟩
  obtain rfl : below F w = v := (below_eq_iff w v).2 hw
  exact adeleTensorEquiv_tmul_snd l x w

private theorem gal_fst (σ : E ≃ₐ[F] E) (a : 𝔸[E]) : (galAd σ a).1 = galInf σ a.1 := by
  obtain ⟨t, rfl⟩ := (adeleTensorEquiv F E).surjective a
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul l x =>
    rw [galAd, galOf_tmul', tensor_fst, tensor_fst, galInf, galOf_tmul']
  | add s t hs ht =>
    rw [map_add, map_add]
    change ((galAd σ) _).1 + ((galAd σ) _).1 = galInf σ (_ + _)
    rw [map_add, hs, ht]

private theorem gal_atFin (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : 𝔸[E]) :
    atFin v (galAd σ a) = galFin σ v (atFin v a) := by
  obtain ⟨t, rfl⟩ := (adeleTensorEquiv F E).surjective a
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul l x =>
    rw [galAd, galOf_tmul', tensor_atFin, tensor_atFin, galFin, galOf_tmul']
  | add s t hs ht =>
    simp only [map_add, hs, ht]

private theorem adele_atFin (v : HeightOneSpectrum (𝓞 F)) (a : 𝔸[F]) :
    atFin v (adeleMap F E a) = incFin E v (a.2 v) := by
  funext ⟨w, hw⟩
  obtain rfl : below F w = v := (below_eq_iff w v).2 hw
  rfl

private theorem gal_adele (σ : E ≃ₐ[F] E) (a : 𝔸[F]) : galAd σ (adeleMap F E a) = adeleMap F E a := by
  have h : adeleMap F E a = adeleTensorEquiv F E ((1 : E) ⊗ₜ a) := by
    rw [adeleTensorEquiv_tmul, map_one, one_mul]
  rw [h, galAd, galOf_tmul', map_one]

private theorem gal_inf (σ : E ≃ₐ[F] E) (x : InfiniteAdeleRing F) :
    galInf σ (infMap F E x) = infMap F E x := by
  have h : infMap F E x =
      GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv (K := F) (L := E) ((1 : E) ⊗ₜ x) := by
    rw [GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_tmul', map_one, one_mul]
  rw [h, galInf, galOf_tmul', map_one]

private theorem gal_algebraMap (σ : E ≃ₐ[F] E) (l : E) :
    galAd σ (algebraMap E 𝔸[E] l) = algebraMap E 𝔸[E] (σ l) := by
  have h (m : E) : algebraMap E 𝔸[E] m = adeleTensorEquiv F E (m ⊗ₜ (1 : 𝔸[F])) := by
    rw [adeleTensorEquiv_tmul, map_one, mul_one]
  rw [h l, galAd, galOf_tmul', ← h]

private theorem mapGL_square {A B C D : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (n : ℕ) (f : A →+* B) (g : B →+* D) (h : A →+* C) (k : C →+* D) (H : ∀ a, g (f a) = k (h a))
    (x : GL (Fin n) A) : mapGL n g (mapGL n f x) = mapGL n k (mapGL n h x) :=
  Units.ext (by ext i j; simpa using H _)

end

theorem UpperTheory.adele_galois_action_baseChange_compat :
    Compat := by
  intro F E _ _ _ _ _ σ n
  refine ⟨fun g => ?_, fun v g => ?_, fun g => ?_, fun v g => ?_, fun g => ?_, fun g => ?_, fun δ => ?_, fun γ => ?_⟩
  · exact mapGL_square n _ _ _ _ (gal_fst σ) g
  · exact mapGL_square n _ _ _ _ (gal_atFin σ v) g
  · exact mapGL_square n _ _ _ _ (fun _ => rfl) g
  · refine Units.ext (Matrix.ext fun i j => ?_)
    change atFin v (adeleMap F E ((g : Matrix (Fin n) (Fin n) 𝔸[F]) i j)) = incFin E v ((finAt v g : Matrix (Fin n) (Fin n) _) i j)
    rw [finAt_apply]
    exact adele_atFin v _
  · refine Units.ext ?_
    ext i j
    simpa using gal_adele σ _
  · refine Units.ext ?_
    ext i j
    simpa using gal_inf σ _
  · refine Units.ext ?_
    ext i j
    exact gal_algebraMap σ ((δ : Matrix (Fin n) (Fin n) E) i j)
  · refine Units.ext ?_
    ext i j
    exact adeleMap_algebraMap (K := F) (L := E) ((γ : Matrix (Fin n) (Fin n) F) i j)
