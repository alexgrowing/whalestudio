import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.PullLocSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.FinTheta

noncomputable section

namespace PI.VolStabW

namespace CompGAux

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.VolStabW.FiniteThetaCoordinates
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R S : Type} [CommRing R] [Algebra F R]
  [CommRing S] [Algebra F S] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem tmap_sigR (φ : R →ₐ[F] S) (x : R ⊗[F] E) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) (sigR R σ x) =
      sigR S σ (Algebra.TensorProduct.map φ (AlgHom.id F E) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tmap_inclR (φ : R →ₐ[F] S) (e : E) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) (inclR R e) = inclR S e := by
  simp [inclR, Algebra.TensorProduct.map_tmul]

theorem map_mem_HR (φ : R →ₐ[F] S) {g : GL (Fin M) (R ⊗[F] E)} (hg : g ∈ HR R σ J) :
    Formalism.UG.bc (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom g ∈ HR S σ J := by
  set ψ : R ⊗[F] E →+* S ⊗[F] E := (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom
  have hg' : Formalism.UG.cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
      (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J := hg
  have hcT : (Formalism.UG.cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E))).map ψ =
      Formalism.UG.cT (sigR S σ) ((g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map ψ) := by
    ext i j
    simp [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, ψ, tmap_sigR]
  have hJ : (JR R J).map ψ = JR S J := by
    ext i j
    simp [JR, Matrix.map_apply, ψ, tmap_inclR]
  show Formalism.UG.cT (sigR S σ) ((g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map ψ) * JR S J *
      (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)).map ψ = JR S J
  rw [← hcT, ← hJ, ← Matrix.map_mul, ← Matrix.map_mul, hg']

def haMap (φ : R →ₐ[F] S) : HA R σ J →* HA S σ J :=
  MonoidHom.codRestrict
    ((Formalism.UG.bc (n := Fin M) (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom).comp
      (HR R σ J).subtype) (HR S σ J) (fun h => map_mem_HR σ J φ h.2)

theorem mat_haMap_apply (φ : R →ₐ[F] S) (h : HA R σ J) (i j : Fin M) :
    ((HA.mat S σ J (haMap σ J φ h) : GL (Fin M) (S ⊗[F] E)) : Matrix (Fin M) (Fin M) _) i j =
      Algebra.TensorProduct.map φ (AlgHom.id F E)
        (((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) i j) := rfl

theorem map_smul_tup (φ : R →ₐ[F] S) {n : ℕ} (h : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E) :
    (fun x i => Algebra.TensorProduct.map φ (AlgHom.id F E) ((h • X) x i)) =
      haMap σ J φ h • (fun x i => Algebra.TensorProduct.map φ (AlgHom.id F E) (X x i)) := by
  funext x i
  show Algebra.TensorProduct.map φ (AlgHom.id F E)
      ((((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _).mulVec (X x)) i) =
    (((HA.mat S σ J (haMap σ J φ h) : GL (Fin M) (S ⊗[F] E)) : Matrix (Fin M) (Fin M) _).mulVec
      (fun j => Algebra.TensorProduct.map φ (AlgHom.id F E) (X x j))) i
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, mat_haMap_apply]

theorem tmap_comp {T : Type} [CommRing T] [Algebra F T] (f : R →ₐ[F] S) (g : S →ₐ[F] T)
    (y : R ⊗[F] E) :
    Algebra.TensorProduct.map g (AlgHom.id F E) (Algebra.TensorProduct.map f (AlgHom.id F E) y) =
      Algebra.TensorProduct.map (g.comp f) (AlgHom.id F E) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

end Gen

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

theorem crd_mulVec_mem (v : HeightOneSpectrum (𝓞 F)) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (m : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) (y : Fin M → Fv F v ⊗[F] E)
    (hm : ∀ i j p, crd b (Fv F v) (m i j) p ∈ v.adicCompletionIntegers F)
    (hy : ∀ j q, crd b (Fv F v) (y j) q ∈ v.adicCompletionIntegers F)
    (hc : ∀ p q k, algebraMap F (Fv F v) (b.repr (b p * b q) k) ∈ v.adicCompletionIntegers F)
    (i : Fin M) (k : Fin d) : crd b (Fv F v) ((m.mulVec y) i) k ∈ v.adicCompletionIntegers F := by
  rw [crd_mulVec]
  exact sum_mem fun j _ => sum_mem fun p _ => sum_mem fun q _ =>
    mul_mem (mul_mem (hm i j p) (hy j q)) (hc p q k)

theorem smul_mem_latV (v : HeightOneSpectrum (𝓞 F)) {d a : ℕ} (b : Module.Basis (Fin d) F E)
    (h : HA (Fv F v) σ J)
    (hm : ∀ i j p, crd b (Fv F v)
      (((HA.mat (Fv F v) σ J h : GL (Fin M) _) : Matrix (Fin M) (Fin M) _) i j) p ∈
        v.adicCompletionIntegers F)
    (hc : ∀ p q k, algebraMap F (Fv F v) (b.repr (b p * b q) k) ∈ v.adicCompletionIntegers F)
    (Y : Fin a → Fin M → Fv F v ⊗[F] E) (hY : Y ∈ latV b v) : h • Y ∈ latV b v := by
  simp only [latV, Set.mem_ofPred_eq] at hY ⊢
  intro x i k
  exact crd_mulVec_mem v b _ (Y x) hm (fun j q => hY x j q) hc i k

theorem eventually_int (g : HA (AF F) σ J) {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v in Filter.cofinite, ∀ i j p, piV F v (crd b (AF F)
      (((HA.mat (AF F) σ J g : GL (Fin M) _) : Matrix (Fin M) (Fin M) _) i j) p) ∈
        v.adicCompletionIntegers F := by
  simp only [Filter.eventually_all]
  intro i j p
  exact (eventually_piV_le_one F _).mono fun v hv => (norm_le_one_iff_mem F v _).1 hv

theorem eventually_struct {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v in Filter.cofinite, ∀ p q k,
      algebraMap F (Fv F v) (b.repr (b p * b q) k) ∈ v.adicCompletionIntegers F := by
  simp only [Filter.eventually_all]
  intro p q k
  refine (eventually_piV_le_one F (algebraMap F (AF F) (b.repr (b p * b q) k))).mono fun v hv => ?_
  rw [AlgHom.commutes] at hv
  exact (norm_le_one_iff_mem F v _).1 hv

theorem compG_gen (a : ℕ) (g : HA (AF F) σ J) :
    ∃ (hInf : HA (Ainf F) σ J) (hv : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J),
    (∀ X : Fin a → Fin M → AF F ⊗[F] E, projInf (g • X) = hInf • projInf X) ∧
    (∀ (v : HeightOneSpectrum (𝓞 F)) (X : Fin a → Fin M → AF F ⊗[F] E),
      projV v (projFin (g • X)) = hv v • projV v (projFin X)) ∧
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v in Filter.cofinite,
      ∀ Y : Fin a → Fin M → Fv F v ⊗[F] E, hv v • Y ∈ latV b v ↔ Y ∈ latV b v := by
  refine ⟨haMap σ J (fstA F) g, fun v => haMap σ J (piV F v) g, ?_, ?_, ?_⟩
  · intro X
    exact map_smul_tup σ J (fstA F) g X
  · intro v X
    have e : ∀ Z : Fin a → Fin M → AF F ⊗[F] E, projV v (projFin Z) =
        fun x i => Algebra.TensorProduct.map (piV F v) (AlgHom.id F E) (Z x i) := by
      intro Z
      funext x i
      exact tmap_comp (sndA F) (evalV F v) (Z x i)
    rw [e, e, map_smul_tup]
  · intro d b
    filter_upwards [eventually_int σ J g b, eventually_int σ J g⁻¹ b, eventually_struct b]
      with v h1 h2 h3
    have hm : ∀ g' : HA (AF F) σ J, (∀ i j p, piV F v (crd b (AF F)
        (((HA.mat (AF F) σ J g' : GL (Fin M) _) : Matrix (Fin M) (Fin M) _) i j) p) ∈
          v.adicCompletionIntegers F) → ∀ i j p, crd b (Fv F v)
        (((HA.mat (Fv F v) σ J (haMap σ J (piV F v) g') : GL (Fin M) _) :
          Matrix (Fin M) (Fin M) _) i j) p ∈ v.adicCompletionIntegers F := by
      intro g' hg' i j p
      rw [mat_haMap_apply, crd_map]
      exact hg' i j p
    intro Y
    constructor
    · intro hY
      have := smul_mem_latV σ J v b (haMap σ J (piV F v) g⁻¹) (hm g⁻¹ h2) h3 _ hY
      rwa [map_inv, inv_smul_smul] at this
    · intro hY
      exact smul_mem_latV σ J v b (haMap σ J (piV F v) g) (hm g h1) h3 Y hY

end Loc

end CompGAux

theorem compG_holds : CompG := by
  intro F E _ _ _ _ _ σ _hCM M J _hJ _ha _hc a _ha1 _ha2 _X0 _hT _hdet g
  exact CompGAux.compG_gen σ J a g

end PI.VolStabW
