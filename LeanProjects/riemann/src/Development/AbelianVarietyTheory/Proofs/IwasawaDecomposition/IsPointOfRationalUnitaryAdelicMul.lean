import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix

noncomputable section
namespace GlobalTheory.Mem.Col2.RatMove

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  (hc : Formalism.BasicNotions.CMData F E) {n : ℕ}

omit [NumberField E] [StarRing E] in

theorem glEquiv_apply_mulVec (g : GL (Fin n) E) (x : Sp E n) : Formalism.UG.glEquiv g x = (g : Matrix (Fin n) (Fin n) E) *ᵥ x := by
  simp [Formalism.UG.glEquiv]

theorem ufGL_eq (γ : UF E n) : ufGL E n γ = (((ratEquiv hc n).symm γ : URat hc n) : GL (Fin n) E) := by
  have hγ : ratHom hc n ((ratEquiv hc n).symm γ) = γ := (ratEquiv hc n).apply_symm_apply γ
  apply Units.ext
  refine Matrix.ext_of_mulVec_single fun j => ?_
  funext i
  have h1 := congrArg (fun g : UF E n => (g : Sp E n ≃ₗ[E] Sp E n) (Pi.single j 1) i) hγ
  simp only [ratHom, MonoidHom.coe_mk, OneHom.coe_mk] at h1
  rw [← glEquiv_apply_mulVec, ← glEquiv_apply_mulVec, h1]
  show Formalism.UG.glEquiv (toGLm E n γ.1) _ i = _
  rw [glEquiv_toGLm]

omit [NumberField E] [StarRing E] in

theorem glEquiv_symm_apply (γ : GL (Fin n) E) (v : Sp E n) :
    (Formalism.UG.glEquiv γ).symm v = ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ v := by
  rw [LinearEquiv.symm_apply_eq]
  simp [Formalism.UG.glEquiv, Matrix.mulVec_mulVec]

theorem pullV_ratMul (γ : GL (Fin n) E) (g : GL (Fin n) (AfE F E)) (x : Sp E n) :
    GlobalTheory.Mem.Col2.pullV (Formalism.UG.bc (iA F E) γ * g) x = GlobalTheory.Mem.Col2.pullV g ((Formalism.UG.glEquiv γ).symm x) := by
  have h := Formalism.L2.Col.pullV_rawSm γ g 1 x
  rw [inv_one, mul_one, Units.val_one, Matrix.one_mulVec] at h
  rw [glEquiv_symm_apply]
  exact h

variable {hc} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem isPtOf_ratMul (γ : URat hc n) {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) :
    IsPtOf hc (Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) * g)
      (((ratHom hc n γ, 1, 1) : UF E n × GLG E n SG × GLQ E n Q) • p) := by
  have hN : Formalism.UG.CS.globLat g (stdLat E n) = p.deco.1.N := by
    rw [← Formalism.UG.P.global_lattice_one_holds F E (Fin n) p.deco.1.N (Module.Finite.iff_fg.2 p.deco.2.lat.fg) p.deco.2.lat.span_eq_top]
    ext w
    refine (h.lat _).symm.trans ?_
    show _ ↔ ((1⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ _ ∈ Formalism.L2.Herm.hatL (F := F) p.deco.1.N
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
  have hst : (1 : GL (Fin n) (AfE F E))⁻¹ ∈
      Formalism.UG.stabGL (Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (stdLat E n)) := by
    rw [inv_one]; exact one_mem _
  have hN2 := Formalism.UG.P.global_lattice_equiv_holds F E (Fin n) (stdLat E n) γ g _ hst
  rw [inv_one, mul_one] at hN2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact mul_mem (ratIn hc n γ).2 h.uni
  · have hc2 := PtExist.carries_globLat (F := F) (Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) * g)
    rw [hN2, hN] at hc2
    exact hc2
  · intro P x hx i hi
    have hx' : (Formalism.UG.glEquiv (γ : GL (Fin n) E)).symm x ∈ p.deco.1.N := (mem_gmap _ _ _).1 hx
    rw [pullV_ratMul]
    exact h.f P _ hx' i hi
  · intro w x hx i
    have hx' : (Formalism.UG.glEquiv (γ : GL (Fin n) E)).symm x ∈ p.deco.1.N := (mem_gmap _ _ _).1 hx
    show HasRes w.1 _ (((((1 : GLG E n SG) w : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)) *ᵥ
      p.deco.1.be w ((Formalism.UG.glEquiv (γ : GL (Fin n) E)).symm x)) i)
    rw [Pi.one_apply, Units.val_one, Matrix.one_mulVec, pullV_ratMul]
    exact h.be w _ hx' i
  · intro P i j
    show _ = algebraMap E _ ((Formalism.UG.glEquiv (γ : GL (Fin n) E) * p.fr P * (((1 : GLQ E n Q) P)⁻¹).1) (Pi.single j 1) i)
    have e1 : (((1 : GLQ E n Q) P)⁻¹).1 = 1 := by simp
    rw [e1, mul_one, LinearEquiv.mul_apply, glEquiv_apply_mulVec, Units.val_mul, Matrix.mul_apply, map_sum]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [h.fr P l j]
    congr 1
    show adAt F P.1 (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) ((γ : GL (Fin n) E) i l)) = _
    rw [adAt_inclE]

theorem isPtOf_ratAd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))) (γ : UF E n) (g : GL (Fin n) (AfE F E))
    (p : DecoF E n ST SG Q), IsPtOf hc g p →
      IsPtOf hc (ratAd F γ * g) (((γ, 1, 1) : UF E n × GLG E n SG × GLQ E n Q) • p) := by
  intro F E _ _ _ _ _ _ hc n ST SG Q γ g p h
  have hγ : ratHom hc n ((ratEquiv hc n).symm γ) = γ := (ratEquiv hc n).apply_symm_apply γ
  have hR : ratAd F γ = Formalism.UG.bc (iA F E) ((((ratEquiv hc n).symm γ : URat hc n)) : GL (Fin n) E) := by
    show Formalism.UG.bc (iA F E) (ufGL E n γ) = _
    rw [ufGL_eq hc]
  have := isPtOf_ratMul ((ratEquiv hc n).symm γ) (ST := ST) (SG := SG) (Q := Q) h
  rw [hγ] at this
  rw [hR]
  exact this

end GlobalTheory.Mem.Col2.RatMove
