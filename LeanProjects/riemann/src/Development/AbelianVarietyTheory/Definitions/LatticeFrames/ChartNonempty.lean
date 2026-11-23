import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm.Model
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7}

section Gen
variable (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n)

theorem mt_mul (g h : GA D V) : mt V (g * h) = mt V g * mt V h := by
  simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

theorem mt_one : mt V (1 : GA D V) = 1 := by
  simp only [Formalism.L2.Theta.mt, map_one, Units.val_one]

theorem finM_mul (g h : GA D V) : finM V hn (g * h) = finM V hn g * finM V hn h := by
  subst hn
  simp only [finM, mt_mul, finCongr_refl, Matrix.reindex_refl_refl]
  exact Matrix.map_mul

theorem finM_one : finM V hn (1 : GA D V) = 1 := by
  subst hn
  simp only [finM, mt_one, finCongr_refl, Matrix.reindex_refl_refl]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem infM_eq (g : GA D V) (τ : D.what₂.Tau) :
    infM θ V hn g τ = ((mt V g).map ((θ τ).comp (infPart D))).reindex (finCongr hn) (finCongr hn) := rfl

theorem infM_mul (g h : GA D V) (τ : D.what₂.Tau) : infM θ V hn (g * h) τ = infM θ V hn g τ * infM θ V hn h τ := by
  subst hn
  simp only [infM_eq, mt_mul, finCongr_refl, Matrix.reindex_refl_refl]
  exact Matrix.map_mul

theorem infM_one (τ : D.what₂.Tau) : infM θ V hn (1 : GA D V) τ = 1 := by
  subst hn
  simp only [infM_eq, mt_one, finCongr_refl, Matrix.reindex_refl_refl]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem infM_unit (g : GA D V) (τ : D.what₂.Tau) : IsUnit (infM θ V hn g τ).det := by
  have h := infM_mul θ V hn g g⁻¹ τ
  rw [mul_inv_cancel, infM_one] at h
  exact Matrix.isUnit_det_of_right_inverse h.symm

def finGL (g : GA D V) : GL (Fin n) (EF D) :=
  ⟨finM V hn g, finM V hn g⁻¹, by rw [← finM_mul, mul_inv_cancel, finM_one], by rw [← finM_mul, inv_mul_cancel, finM_one]⟩

theorem toEAf_conj (a : AE D) :
    toEAf D (cA D a) = Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (toEAf D a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rfl
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingHom.map_add, hx, hy]

theorem toEAf_inc (e : D.host.E) : toEAf D (incA D e) = inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) e := rfl

theorem finGL_mem (g : GA D V) :
    finGL V hn g ∈ UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
  subst hn
  have hg : cT (cA D) (mt V g) * V.gram.map (incA D) * mt V g = V.gram.map (incA D) := g.2
  have h2 := congrArg (fun M => M.map (toEAf D)) hg
  simp only [Matrix.map_mul] at h2
  change cT _ (finM V rfl g) * _ * finM V rfl g = _
  simp only [finM, finCongr_refl, Matrix.reindex_refl_refl]
  have e1 : cT (Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ((mt V g).map (toEAf D)) =
      (cT (cA D) (mt V g)).map (toEAf D) := by
    ext i j; simp only [cT, Matrix.transpose_apply, Matrix.map_apply, toEAf_conj]
  have e2 : V.gram.map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) = (V.gram.map (incA D)).map (toEAf D) := rfl
  rw [e1, e2]; exact h2

def trFr {G : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ} (g : GA D V) (y : Frames G) : Frames G :=
  ⟨fun τ => infM θ V hn g τ * y.1 τ, fun τ => by rw [Matrix.det_mul]; exact (infM_unit θ V hn g τ).mul (y.2 τ)⟩

variable {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (S : StepLevel D.host.F D.host.E (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) T f bad) {cl : Type}
  (yc : cl → UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))

theorem exists_dec (hy : Function.Surjective (fun c => (Quotient.mk'' (yc c) : Cls S))) (g : GA D V) :
    ∃ p, IsDec S yc (finM V hn g) p := by
  obtain ⟨c, hc⟩ := hy (Quotient.mk'' ⟨finGL V hn g, finGL_mem V hn g⟩)
  obtain ⟨a, ha, b, hb, hab⟩ := (DoubleCoset.eq _ _ (yc c) _).1 hc
  obtain ⟨γ, hγ, e⟩ := Subgroup.mem_subgroupOf.1 ha
  refine ⟨(c, γ, ⟨b.1, Subgroup.mem_subgroupOf.1 hb⟩), hγ, ?_⟩
  have := congrArg (fun x => x.1.1) hab
  simp only at this
  rw [e]; exact this

set_option maxHeartbeats 2000000 in

theorem rdS_res (hy : Function.Surjective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (Ψ) (hΨ : Ψ ∈ AdFun S (embT D)) (y : Frames (gramC _ (embT D))) (g : GA D V) :
    rdS θ V hn S yc (fun c => Ψ (yc c)) y g = Ψ ⟨finGL V hn g, finGL_mem V hn g⟩ (trFr θ V hn g y) := by
  have h := exists_dec V hn S yc hy g
  rw [rdS, dif_pos h]
  obtain ⟨h1, h2⟩ := h.choose_spec
  generalize h.choose = p at h1 h2 ⊢
  have hi : ∀ τ, atInf (embT D) p.2.1.1 τ * atInf (embT D) (p.2.1⁻¹ : GL (Fin n) D.host.E).1 τ = 1 := by
    intro τ
    simp only [atInf]
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hu : ∀ τ, IsUnit (atInf (embT D) (p.2.1⁻¹ : GL (Fin n) D.host.E).1 τ * infM θ V hn g τ * y.1 τ).det := by
    intro τ
    rw [Matrix.det_mul, Matrix.det_mul]
    exact ((Matrix.isUnit_det_of_left_inverse (hi τ)).mul (infM_unit θ V hn g τ)).mul (y.2 τ)
  rw [atFr, dif_pos hu]
  refine (hΨ p.2.1 h1 (yc p.1) _ p.2.2 (Units.ext h2) _ _ ?_).symm
  intro τ
  simp only [trFr]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hi, Matrix.one_mul]

theorem rdS_left (hθ : IsInfFam θ) (hy : Function.Surjective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (Ψ) (hΨ : Ψ ∈ AdFun S (embT D)) (y : Frames (gramC _ (embT D))) (γ : GA D V) (hγ : γ ∈ GQ V) (g : GA D V) :
    rdS θ V hn S yc (fun c => Ψ (yc c)) y (γ * g) = rdS θ V hn S yc (fun c => Ψ (yc c)) y g := by
  rw [rdS_res θ V hn S yc hy Ψ hΨ, rdS_res θ V hn S yc hy Ψ hΨ]
  subst hn
  obtain ⟨δ, hδ, e⟩ := Subgroup.mem_subgroupOf.1 hγ
  have e' : mt V γ = δ.1.map (incA D) := congrArg Units.val e.symm
  have := hΨ δ hδ ⟨finGL V rfl g, finGL_mem V rfl g⟩ ⟨finGL V rfl (γ * g), finGL_mem V rfl (γ * g)⟩ 1 (by
      apply Units.ext
      change finM V rfl (γ * g) = _
      rw [finM_mul]
      simp only [OneMemClass.coe_one, mul_one, Units.val_mul]
      congr 1
      simp only [finM, e', finCongr_refl, Matrix.reindex_refl_refl]
      rfl)
    (trFr θ V rfl (γ * g) y) (trFr θ V rfl g y) (by
      intro τ
      simp only [trFr, infM_mul, Matrix.mul_assoc]
      congr 1
      simp only [infM_eq, e', finCongr_refl, Matrix.reindex_refl_refl]
      ext i j
      exact (hθ τ).1 _)
  simpa using this

theorem rdS_right_inf (ψ : cl → Frames (gramC (V.gram.reindex (finCongr hn) (finCongr hn)) (embT D)) → ℂ)
    (y : Frames (gramC _ (embT D))) (g k : GA D V) (hk : finM V hn k = 1) :
    rdS θ V hn S yc ψ y (g * k) = rdS θ V hn S yc ψ (trFr θ V hn k y) g := by
  have e : finM V hn (g * k) = finM V hn g := by rw [finM_mul, hk, mul_one]
  simp only [rdS, e, infM_mul, trFr, Matrix.mul_assoc]

set_option maxHeartbeats 2000000 in

theorem rdS_right_lev (hy : Function.Surjective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (Ψ) (hΨ : Ψ ∈ AdFun S (embT D)) (y : Frames (gramC _ (embT D))) (g k : GA D V) (κ : S.U)
    (hk : finM V hn k = κ.1.1) (hk' : ∀ τ, infM θ V hn k τ = 1) :
    rdS θ V hn S yc (fun c => Ψ (yc c)) y (g * k) = (S.chi κ : ℂ) * rdS θ V hn S yc (fun c => Ψ (yc c)) y g := by
  rw [rdS_res θ V hn S yc hy Ψ hΨ, rdS_res θ V hn S yc hy Ψ hΨ]
  refine hΨ 1 (one_mem _) _ _ κ ?_ _ _ ?_
  · apply Units.ext
    change finM V hn (g * k) = _
    rw [finM_mul, hk]
    simp only [map_one, one_mul, Units.val_mul]
    rfl
  · intro τ
    simp only [trFr, infM_mul, hk', atInf, Units.val_one, mul_one]
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem rdS_at_rep (hy : Function.Surjective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (Ψ) (hΨ : Ψ ∈ AdFun S (embT D)) (y : Frames (gramC _ (embT D))) (g : GA D V) (c : cl)
    (hk : finM V hn g = (yc c).1.1) (hk' : ∀ τ, infM θ V hn g τ = 1) :
    rdS θ V hn S yc (fun c => Ψ (yc c)) y g = Ψ (yc c) y := by
  rw [rdS_res θ V hn S yc hy Ψ hΨ]
  congr 1
  · exact Subtype.ext (Units.ext hk)
  · apply Subtype.ext; funext τ; simp only [trFr, hk', Matrix.one_mul]

theorem rdS_add (ψ ψ' : cl → Frames (gramC (V.gram.reindex (finCongr hn) (finCongr hn)) (embT D)) → ℂ) (y) (g : GA D V) :
    rdS θ V hn S yc (ψ + ψ') y g = rdS θ V hn S yc ψ y g + rdS θ V hn S yc ψ' y g := by
  simp only [rdS, atFr]
  split_ifs
  · exact mul_add _ _ _
  · simp
  · simp

end Gen

variable {u : D.what₂.Word}

theorem chart_rd {i : ℕ} {hi : i ≤ D.R.m} (Q : Chart D u i hi) (θ : InfFam D)
    (ψ : (D.mem u).C.cls i → (D.mem u).C.Y i → ℂ) (Ψ) (hΨ : Ψ ∈ AdFun Q.K.lev (embT D))
    (hψ : ∀ c z, ψ (Q.inc c) (Q.eY.symm z) = Ψ (Q.K.y c) z) (y : (D.mem u).C.Y i) (g : GA D (D.sp.X i)) :
    Q.rd θ ψ y g = Ψ ⟨finGL _ (rankN D i hi) g, finGL_mem _ (rankN D i hi) g⟩ (trFr θ _ (rankN D i hi) g (Q.eY y)) := by
  have e : (fun c z => ψ (Q.inc c) (Q.eY.symm z)) = fun c => Ψ (Q.K.y c) := by funext c z; exact hψ c z
  rw [Chart.rd, e]
  exact rdS_res θ _ (rankN D i hi) Q.K.lev Q.K.y Q.K.y_bij.2 Ψ hΨ _ g

theorem chart_nonempty {i : ℕ} {hi : i ≤ D.R.m} (Q : Chart D u i hi) : Nonempty Q.cl :=
  ⟨(Q.K.y_bij.2 (Quotient.mk'' 1)).choose⟩

variable {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (F : FormsTiedSym D u Ch chOf)

theorem mid_left (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ D.R.m) (β : Ch i) (θ : InfFam D) (hθ : IsInfFam θ)
    (ψ : (D.mem u).C.cls i → (D.mem u).C.Y i → ℂ) (hψ : ψ ∈ (D.fm u).Fi i) (y) (γ) (hγ : γ ∈ GQ (D.sp.X i)) (g) :
    rd F θ i (le_of_succ_m h2) β ψ y (γ * g) = rd F θ i (le_of_succ_m h2) β ψ y g := by
  have hc : chart F i (le_of_succ_m h2) β = midChart F i h1 h2 β := by
    rw [chart, dif_neg (by omega)]
  obtain ⟨Ψ, hΨ, e⟩ := ((F.valC i h1 h2).Fi ψ).1 hψ β
  rw [rd, hc, Chart.rd]
  have e' : (fun c z => ψ ((midChart F i h1 h2 β).inc c) ((midChart F i h1 h2 β).eY.symm z)) =
    fun c => Ψ ((midChart F i h1 h2 β).K.y c) := e.symm
  rw [e']
  exact rdS_left θ _ (rankN D i (le_of_succ_m h2)) _ _ hθ (midChart F i h1 h2 β).K.y_bij.2 Ψ hΨ.1 _ γ hγ g

theorem end_left (i : ℕ) (hi : i ≤ D.R.m) (h : i = 0 ∨ i = D.R.m) (β : Ch i) (θ : InfFam D) (hθ : IsInfFam θ)
    (ψ : (D.mem u).C.cls i → (D.mem u).C.Y i → ℂ) (hψ : ψ ∈ (D.fm u).Fi i) (y) (γ) (hγ : γ ∈ GQ (D.sp.X i)) (g) :
    rd F θ i hi β ψ y (γ * g) = rd F θ i hi β ψ y g := by
  have hc : chart F i hi β = endChart F i hi h := by rw [chart, dif_pos h]
  obtain ⟨Ψ, hΨ, e⟩ := ((F.val i hi h).Fi ψ).1 hψ
  rw [rd, hc, Chart.rd]
  have e' : (fun c z => ψ ((endChart F i hi h).inc c) ((endChart F i hi h).eY.symm z)) =
    fun c => Ψ ((endChart F i hi h).K.y c) := e.symm
  rw [e']
  exact rdS_left θ _ (rankN D i hi) _ _ hθ (endChart F i hi h).K.y_bij.2 Ψ hΨ.1 _ γ hγ g

theorem rdP_left (θ : InfFam D) (hθ : IsInfFam θ) (z : (D.mem u).P.Wrow) (hz : z ∈ (D.fm u).ptC) (y) (γ) (hγ : γ ∈ GQ D.sp.X') (g) :
    rdP F θ z y (γ * g) = rdP F θ z y g := by
  obtain ⟨Ψ, hΨ, e⟩ := (F.valP.ptC z).1 hz
  rw [rdP, ← e]
  exact rdS_left θ _ (rankP D) _ _ hθ F.clsP.y_bij.2 Ψ hΨ.1 _ γ hγ g

end GlobalTheory.AdForm.Model
