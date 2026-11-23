import Mathlib
import GroundTheory.PAdicHodge.KerFontaineThetaCompFrobeniusEquivSymmPow
import GroundTheory.PAdicHodge.AInfTopology
import GroundTheory.PAdicHodge.TiltMap
import GroundTheory.PAdicHodge.TiltAlgebra
import GroundTheory.PAdicHodge.GaloisOnCp
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace AInf

section Functor

variable {K L M : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField L] [IsUltrametricDist L] [NontriviallyNormedField M]
  [IsUltrametricDist M]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField L p]
  [IsPerfectoidField M p]

variable (p) in

def map (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) : AInf K p →+* AInf L p :=
  WittVector.map (preTiltMap p φ hφ)

theorem map_coeff (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (x : AInf K p) (n : ℕ) :
    (map p φ hφ x).coeff n = preTiltMap p φ hφ (x.coeff n) :=
  WittVector.map_coeff _ _ _

theorem map_teichmuller (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (x : PreTilt (normInteger K) p) :
    map p φ hφ (WittVector.teichmuller p x) = WittVector.teichmuller p (preTiltMap p φ hφ x) :=
  WittVector.map_teichmuller p _ x

theorem fontaineTheta_map (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (w : AInf K p) :
    WittVector.fontaineTheta (normInteger L) p (map p φ hφ w) =
      integerMap φ hφ (WittVector.fontaineTheta (normInteger K) p w) :=
  fontaineTheta_map_preTiltMap φ hφ w

theorem map_congr {φ ψ : K →+* L} (h : φ = ψ) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) :
    map p φ hφ = map p ψ hψ := by
  subst h; rfl

theorem map_comp (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (ψ : L →+* M) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) :
    map p (ψ.comp φ) (norm_comp_eq hφ hψ) = (map p ψ hψ).comp (map p φ hφ) := by
  refine RingHom.ext fun x => WittVector.ext fun n => ?_
  rw [RingHom.comp_apply, map_coeff, map_coeff, map_coeff, preTiltMap_comp, RingHom.comp_apply]

theorem preTiltMap_id (x : PreTilt (normInteger K) p) :
    preTiltMap p (RingHom.id K) (fun _ => rfl) x = x := by
  refine Perfection.ext fun n => ?_
  rw [coeff_preTiltMap]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (Perfection.coeff (ModP (normInteger K) p) p n x)
  rw [← ha, modPMap_mk]
  congr 1

theorem map_id : map p (RingHom.id K) (fun _ => rfl) = RingHom.id (AInf K p) := by
  refine RingHom.ext fun x => WittVector.ext fun n => ?_
  rw [map_coeff, preTiltMap_id, RingHom.id_apply]

theorem map_frobeniusEquiv (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (x : AInf K p) :
    map p φ hφ (WittVector.frobeniusEquiv p _ x) = WittVector.frobeniusEquiv p _ (map p φ hφ x) := by
  refine WittVector.ext fun n => ?_
  rw [map_coeff, WittVector.frobeniusEquiv_coeff, WittVector.frobeniusEquiv_coeff, map_coeff,
    map_pow]

theorem map_frobeniusEquiv_symm (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (x : AInf K p) :
    map p φ hφ ((WittVector.frobeniusEquiv p _).symm x) =
      (WittVector.frobeniusEquiv p _).symm (map p φ hφ x) := by
  refine WittVector.ext fun n => ?_
  rw [map_coeff, WittVector.frobeniusEquiv_symm_coeff, WittVector.frobeniusEquiv_symm_coeff,
    map_coeff, RingHom.map_frobeniusEquiv_symm]

omit [IsUltrametricDist K] in

theorem norm_toRingHom_apply (σ : K ≃+* K) (hσ : ∀ x, ‖σ x‖ = ‖x‖) (x : K) :
    ‖(σ : K →+* K) x‖ = ‖x‖ :=
  hσ x

omit [IsUltrametricDist K] in

theorem norm_symm_toRingHom_apply (σ : K ≃+* K) (hσ : ∀ x, ‖σ x‖ = ‖x‖) (x : K) :
    ‖(σ.symm : K →+* K) x‖ = ‖x‖ := by
  change ‖σ.symm x‖ = ‖x‖
  rw [← hσ, RingEquiv.apply_symm_apply]

variable (p) in

def mapEquiv (σ : K ≃+* K) (hσ : ∀ x, ‖σ x‖ = ‖x‖) : AInf K p ≃+* AInf K p :=
  RingEquiv.ofRingHom (map p (σ : K →+* K) (norm_toRingHom_apply σ hσ))
    (map p (σ.symm : K →+* K) (norm_symm_toRingHom_apply σ hσ))
    (by
      rw [← map_comp, ← map_id]
      exact map_congr (RingHom.ext fun x => σ.apply_symm_apply x) _ _)
    (by
      rw [← map_comp, ← map_id]
      exact map_congr (RingHom.ext fun x => σ.symm_apply_apply x) _ _)

end Functor

section Galois

variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem norm_galCp_toRingHom (σ : Gal(PadicAlgCl p/K)) (x : ℂ_[p]) :
    ‖(galCp σ : ℂ_[p] →+* ℂ_[p]) x‖ = ‖x‖ :=
  norm_galCp σ x

def galMap (σ : Gal(PadicAlgCl p/K)) : AInf ℂ_[p] p →+* AInf ℂ_[p] p :=
  map p (galCp σ : ℂ_[p] →+* ℂ_[p]) (norm_galCp_toRingHom σ)

theorem galMap_one : galMap (1 : Gal(PadicAlgCl p/K)) = RingHom.id _ := by
  rw [galMap, ← map_id]
  exact map_congr (RingHom.ext fun x => by rw [galCp_one]; rfl) _ _

theorem galMap_mul (σ τ : Gal(PadicAlgCl p/K)) : galMap (σ * τ) = (galMap σ).comp (galMap τ) := by
  rw [galMap, galMap, galMap, ← map_comp]
  exact map_congr (RingHom.ext fun x => by rw [galCp_mul]; rfl) _ _

instance instMulSemiringActionGal : MulSemiringAction Gal(PadicAlgCl p/K) (AInf ℂ_[p] p) where
  smul σ x := galMap σ x
  one_smul x := by
    change galMap 1 x = x
    rw [galMap_one, RingHom.id_apply]
  mul_smul σ τ x := by
    change galMap (σ * τ) x = galMap σ (galMap τ x)
    rw [galMap_mul, RingHom.comp_apply]
  smul_zero σ := map_zero (galMap σ)
  smul_add σ := map_add (galMap σ)
  smul_one σ := map_one (galMap σ)
  smul_mul σ := map_mul (galMap σ)

theorem gal_smul_def (σ : Gal(PadicAlgCl p/K)) (x : AInf ℂ_[p] p) : σ • x = galMap σ x := rfl

theorem gal_smul_coeff (σ : Gal(PadicAlgCl p/K)) (x : AInf ℂ_[p] p) (n : ℕ) :
    (σ • x).coeff n = preTiltMap p (galCp σ : ℂ_[p] →+* ℂ_[p]) (norm_galCp_toRingHom σ) (x.coeff n) :=
  map_coeff _ _ x n

theorem gal_smul_teichmuller (σ : Gal(PadicAlgCl p/K)) (x : PreTilt (normInteger ℂ_[p]) p) :
    σ • (WittVector.teichmuller p x : AInf ℂ_[p] p) =
      WittVector.teichmuller p (preTiltMap p (galCp σ : ℂ_[p] →+* ℂ_[p]) (norm_galCp_toRingHom σ) x) :=
  map_teichmuller _ _ x

theorem coe_untilt_gal (σ : Gal(PadicAlgCl p/K)) (x : PreTilt (normInteger ℂ_[p]) p) :
    ((PreTilt.untilt (preTiltMap p (galCp σ : ℂ_[p] →+* ℂ_[p]) (norm_galCp_toRingHom σ) x) :
      normInteger ℂ_[p]) : ℂ_[p]) = σ • ((PreTilt.untilt x : normInteger ℂ_[p]) : ℂ_[p]) := by
  rw [untilt_preTiltMap, coe_integerMap]
  rfl

theorem fontaineTheta_gal_smul (σ : Gal(PadicAlgCl p/K)) (x : AInf ℂ_[p] p) :
    ((WittVector.fontaineTheta (normInteger ℂ_[p]) p (σ • x) : normInteger ℂ_[p]) : ℂ_[p]) =
      σ • ((WittVector.fontaineTheta (normInteger ℂ_[p]) p x : normInteger ℂ_[p]) : ℂ_[p]) := by
  rw [gal_smul_def, galMap, fontaineTheta_map, coe_integerMap]
  rfl

theorem gal_smul_frobeniusEquiv (σ : Gal(PadicAlgCl p/K)) (x : AInf ℂ_[p] p) :
    σ • WittVector.frobeniusEquiv p _ x = WittVector.frobeniusEquiv p _ (σ • x) :=
  map_frobeniusEquiv _ _ x

end Galois

end AInf

end GroundTheory.PAdicHodge
