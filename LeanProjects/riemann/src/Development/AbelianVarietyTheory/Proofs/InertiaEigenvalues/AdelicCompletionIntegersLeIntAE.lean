import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCoverFormsMulComponentFunction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedFieldFibres
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameHeckeCharTrivialOnFiniteUnitsCongOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqOneOfTrivialFinitePartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdelicCharacterPowEqOneFiniteIdelesOfOrderDvd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNthRootIdeleFinitePartOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntUnitRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdeleUnitCongrOne

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistRat.Right
variable {D : D7}

def iI (F : Type) [Field F] [NumberField F] : Ainf F →ₗ[F] AF F where
  toFun x := ((x, 0) : Ainf F × Af F)
  map_add' x y := by
    show ((x + y, 0) : Ainf F × Af F) = ((x, 0) : Ainf F × Af F) + ((y, 0) : Ainf F × Af F)
    rw [Prod.mk_add_mk, add_zero]
  map_smul' c x := by
    apply Prod.ext
    · show c • x = (c • ((x, 0) : AF F)).1
      rfl
    · show (0 : Af F) = (c • ((x, 0) : AF F)).2
      show (0 : Af F) = algebraMap F (Af F) c * 0
      simp

def iF (F : Type) [Field F] [NumberField F] : Af F →ₗ[F] AF F where
  toFun x := ((0, x) : Ainf F × Af F)
  map_add' x y := by
    show ((0, x + y) : Ainf F × Af F) = ((0, x) : Ainf F × Af F) + ((0, y) : Ainf F × Af F)
    rw [Prod.mk_add_mk, add_zero]
  map_smul' c x := by
    apply Prod.ext
    · show (0 : Ainf F) = (c • ((0, x) : AF F)).1
      first
        | (show (0 : Ainf F) = c • (0 : Ainf F); simp)
        | (show (0 : Ainf F) = algebraMap F (Ainf F) c * 0; simp)
        | (show (0 : Ainf F) = (algebraMap F (AF F) c * ((0, x) : AF F)).1; show (0 : Ainf F) = (algebraMap F (AF F) c).1 * 0; simp)
    · show c • x = (c • ((0, x) : AF F)).2
      rfl
example (F : Type) [Field F] [NumberField F] (x : Ainf F) : fstA F (iI F x) = x := rfl
example (F : Type) [Field F] [NumberField F] (x : Ainf F) : sndA F (iI F x) = 0 := rfl

def jI (D : D7) : Ainf D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D := TensorProduct.map (iI D.host.F) LinearMap.id
def jF (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D := TensorProduct.map (iF D.host.F) LinearMap.id

theorem recon (x : AE D) : jI D (infPart D x) + jF D (finPart D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p q =>
    show iI D.host.F (fstA D.host.F p) ⊗ₜ q + iF D.host.F (sndA D.host.F p) ⊗ₜ q = p ⊗ₜ q
    rw [← TensorProduct.add_tmul]
    congr 1
    show ((p.1, 0) : Ainf D.host.F × Af D.host.F) + ((0, p.2) : Ainf D.host.F × Af D.host.F) = p
    rw [Prod.mk_add_mk, add_zero, zero_add]
    rfl
  | add p q hp hq =>
    rw [RingHom.map_add, RingHom.map_add, LinearMap.map_add, LinearMap.map_add]
    conv_rhs => rw [← hp, ← hq]
    abel

theorem infPart_jI (a : Ainf D.host.F ⊗[D.host.F] D.host.E) : infPart D (jI D a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul p q => rfl
  | add p q hp hq => rw [LinearMap.map_add, RingHom.map_add, hp, hq]

theorem finPart_jI (a : Ainf D.host.F ⊗[D.host.F] D.host.E) : finPart D (jI D a) = 0 := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul p q =>
    show (sndA D.host.F (iI D.host.F p)) ⊗ₜ[D.host.F] q = 0
    show (0 : Af D.host.F) ⊗ₜ[D.host.F] q = 0
    exact TensorProduct.zero_tmul _ _
  | add p q hp hq => rw [LinearMap.map_add, RingHom.map_add, hp, hq, add_zero]

theorem infPart_jF (b : Af D.host.F ⊗[D.host.F] D.host.E) : infPart D (jF D b) = 0 := by
  induction b using TensorProduct.induction_on with
  | zero => simp
  | tmul p q =>
    show (fstA D.host.F (iF D.host.F p)) ⊗ₜ[D.host.F] q = 0
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] q = 0
    exact TensorProduct.zero_tmul _ _
  | add p q hp hq => rw [LinearMap.map_add, RingHom.map_add, hp, hq, add_zero]

theorem finPart_jF (b : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (jF D b) = b := by
  induction b using TensorProduct.induction_on with
  | zero => simp
  | tmul p q => rfl
  | add p q hp hq => rw [LinearMap.map_add, RingHom.map_add, hp, hq]

theorem ext_parts {a b : AE D} (h1 : infPart D a = infPart D b) (h2 : finPart D a = finPart D b) : a = b := by
  rw [← recon a, ← recon b, h1, h2]

theorem exists_unit_parts (a : (Ainf D.host.F ⊗[D.host.F] D.host.E)ˣ) (b : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
    ∃ Y : (AE D)ˣ, infPart D (Y : AE D) = a ∧ finPart D (Y : AE D) = b := by
  have hI : ∀ a' b', infPart D (jI D a' + jF D b') = a' := fun a' b' => by
    rw [RingHom.map_add, infPart_jI, infPart_jF, add_zero]
  have hF : ∀ a' b', finPart D (jI D a' + jF D b') = b' := fun a' b' => by
    rw [RingHom.map_add, finPart_jI, finPart_jF, zero_add]
  have h1 : (jI D (a : _) + jF D (b : _)) * (jI D ((a⁻¹ : (Ainf D.host.F ⊗[D.host.F] D.host.E)ˣ) : _) +
      jF D ((b⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : _)) = 1 := by
    apply ext_parts
    · rw [RingHom.map_mul, hI, hI, Units.mul_inv, RingHom.map_one]
    · rw [RingHom.map_mul, hF, hF, Units.mul_inv, RingHom.map_one]
  exact ⟨⟨_, _, h1, by rw [mul_comm]; exact h1⟩, hI _ _, hF _ _⟩

end GlobalTheory.TwistRat.Right

namespace GlobalTheory.TwistRat.Right
variable {D : D7}

theorem char_arch_one {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (h : ChrEq c χ) {n : ℕ} (hn : 0 < n)
    (ho : χ.OrderDvd n) (x : (AE D)ˣ) (hx : finPart D (x : AE D) = 1) : c x = 1 := by
  have key := GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D (c ^ n)
    ⟨h.1.1.pow n, fun x => by rw [MonoidHom.pow_apply, h.1.2 x, one_pow]⟩
    (GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd D c χ h n ho)
  obtain ⟨y, rfl⟩ := GlobalTheory.IdeleDiv.exists_pow_eq_of_finPart_eq_one D n hn x hx
  rw [map_pow]
  exact key y

theorem isDetRoot_mul {V : HSp D} {g g' : GA D V} {x x' : (AE D)ˣ} (h : IsDetRoot V g x) (h' : IsDetRoot V g' x') :
    IsDetRoot V (g * g') (x * x') := by
  unfold IsDetRoot at *
  rw [map_mul, Units.val_mul, Units.val_mul, Matrix.det_mul, RingHom.map_mul]
  conv_lhs => rw [h, h']
  ring

end GlobalTheory.TwistRat.Right

namespace GlobalTheory.TwistRat.Right
variable {D : D7}
theorem infPart_sigR (x : AE D) : infPart D (sigR (AF D.host.F) D.sp.cm.sig x) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p q => rfl
  | add p q hp hq => rw [RingHom.map_add, RingHom.map_add, hp, hq, RingHom.map_add, RingHom.map_add]
theorem finPart_sigR (x : AE D) : finPart D (sigR (AF D.host.F) D.sp.cm.sig x) = sigR (Af D.host.F) D.sp.cm.sig (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p q => rfl
  | add p q hp hq => rw [RingHom.map_add, RingHom.map_add, hp, hq, RingHom.map_add, RingHom.map_add]
theorem sigR_tmul_one (b : Af D.host.F) : sigR (Af D.host.F) D.sp.cm.sig (b ⊗ₜ[D.host.F] (1 : D.host.E)) = b ⊗ₜ[D.host.F] (1 : D.host.E) := by
  show b ⊗ₜ[D.host.F] D.sp.cm.sig 1 = _
  rw [map_one]
theorem adelicCompletion_integers_le_intAE (w) (hw : w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E))) : w ∈ intAE D := by
  refine (AddSubgroup.closure_le _).2 ?_ hw
  rintro _ ⟨a, ha, _, ⟨r, rfl⟩, rfl⟩
  exact AddSubgroup.subset_closure ⟨a, ha, r, rfl⟩
theorem one_mem_intAE : (1 : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨1, fun v => by simp [evalV], 1, by simp; rfl⟩
theorem finPart_det (V : HSp D) (u : GA D V) :
    finPart D (matHom V u).1.det = (finHom V u).1.det := by
  rw [RingHom.map_det]
  rfl
end GlobalTheory.TwistRat.Right

namespace GlobalTheory.TwistRat.Right

set_option maxHeartbeats 1600000 in

theorem exists_root_one {D : D7} {V : HSp D} {M pd : ℕ} {k : Type} [Field k] {σ : k →+* ℂ}
    {δ : Formalism.L2.Host.HChar D.host.E} {δc : (AE D)ˣ →* Circle} (hA : IsAuxiliarySplitSquarefreeLevel D M pd) (hT : IsTwist pd σ δ δc)
    {u : GA D V} (hu : GlobalTheory.Member.FinCong V (M * pd) u) (y₀ : (AE D)ˣ) (hy₀ : IsDetRoot V u y₀) :
    ∃ y, IsDetRoot V u y ∧ δc y = 1 := by
  obtain ⟨hc, ⟨n, hn, ho⟩, -, ht, hunr, -⟩ := hT
  have hpd : pd ≠ 0 := fun h => by simpa [h] using hA.1
  have hu' : GlobalTheory.Member.FinCong V pd u := fun z hz => by
    obtain ⟨y, hy, e⟩ := hu z hz
    exact ⟨M • y, AddSubgroup.nsmul_mem _ hy M, by rw [e, mul_comm, mul_nsmul]; exact smul_comm M pd y⟩
  obtain ⟨w, hw, hzw⟩ := GlobalTheory.DetFibre.det_cong_of_finCong V pd hpd u hu'
  have hw' := adelicCompletion_integers_le_intAE w hw
  obtain ⟨zf, hzf⟩ : ∃ zf : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ, (zf : Af D.host.F ⊗[D.host.F] D.host.E) = (finHom V u).1.det :=
    ⟨Units.map (finPart D).toMonoidHom (Matrix.GeneralLinearGroup.det (matHom V u)), finPart_det V u⟩
  have hcong : (zf : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = pd • w := by rw [hzf]; exact hzw
  have hzint : (zf : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D := by
    rw [← sub_add_cancel (zf : Af D.host.F ⊗[D.host.F] D.host.E) 1, hcong]
    exact add_mem (AddSubgroup.nsmul_mem _ hw' pd) one_mem_intAE
  have hroot : (Units.map (finPart D).toMonoidHom y₀ : Af D.host.F ⊗[D.host.F] D.host.E) =
      zf * sigR (Af D.host.F) D.sp.cm.sig (Units.map (finPart D).toMonoidHom y₀ : Af D.host.F ⊗[D.host.F] D.host.E) := by
    show finPart D (y₀ : AE D) = _ * sigR (Af D.host.F) D.sp.cm.sig (finPart D (y₀ : AE D))
    rw [hzf, ← finPart_det, ← finPart_sigR, ← RingHom.map_mul]
    exact congrArg (finPart D) hy₀
  obtain ⟨y₁, hy₁, hy₁', hy₁r⟩ := GlobalTheory.IntegralHilbertNinety.exists_int_unit_root D zf hzint ⟨_, hroot⟩
  obtain ⟨b, y₂, hy₂, hy₂i, hy₂i', w₂, hw₂, hy₂c⟩ := GlobalTheory.UnitRootCong.exists_adele_unit_congr_one D pd hA.1 zf y₁ hy₁ hy₁' hy₁r ⟨w, hw', hcong⟩
  obtain ⟨Yf, hYf1, hYf2⟩ := exists_unit_parts (D := D) 1 y₂
  obtain ⟨Yi, hYi1, hYi2⟩ := exists_unit_parts (D := D) (Units.map (infPart D).toMonoidHom y₀) 1
  have hYI : infPart D ((Yf * Yi : (AE D)ˣ) : AE D) = infPart D (y₀ : AE D) := by
    simp only [Units.val_mul, RingHom.map_mul, hYf1, hYi1, Units.val_one, one_mul]
    rfl
  have hYF : finPart D ((Yf * Yi : (AE D)ˣ) : AE D) = (y₂ : Af D.host.F ⊗[D.host.F] D.host.E) := by
    simp only [Units.val_mul, RingHom.map_mul, hYf2, hYi2, Units.val_one, mul_one]
  refine ⟨Yf * Yi, ?_, ?_⟩
  · unfold IsDetRoot
    generalize ((Yf * Yi : (AE D)ˣ) : AE D) = Y at hYI hYF ⊢
    apply ext_parts
    · calc infPart D Y = infPart D (y₀ : AE D) := hYI
        _ = infPart D ((matHom V u).1.det * sigR (AF D.host.F) D.sp.cm.sig (y₀ : AE D)) := congrArg (infPart D) hy₀
        _ = infPart D (matHom V u).1.det * infPart D (sigR (AF D.host.F) D.sp.cm.sig (y₀ : AE D)) := (infPart D).map_mul _ _
        _ = infPart D (matHom V u).1.det * sigR (Ainf D.host.F) D.sp.cm.sig (infPart D (y₀ : AE D)) :=
          congrArg (infPart D (matHom V u).1.det * ·) (infPart_sigR _)
        _ = infPart D (matHom V u).1.det * sigR (Ainf D.host.F) D.sp.cm.sig (infPart D Y) :=
          congrArg (fun t => infPart D (matHom V u).1.det * sigR (Ainf D.host.F) D.sp.cm.sig t) hYI.symm
        _ = infPart D (matHom V u).1.det * infPart D (sigR (AF D.host.F) D.sp.cm.sig Y) :=
          congrArg (infPart D (matHom V u).1.det * ·) (infPart_sigR _).symm
        _ = infPart D ((matHom V u).1.det * sigR (AF D.host.F) D.sp.cm.sig Y) := ((infPart D).map_mul _ _).symm
    · have e2 : (y₂ : Af D.host.F ⊗[D.host.F] D.host.E) = zf * sigR (Af D.host.F) D.sp.cm.sig (y₂ : Af D.host.F ⊗[D.host.F] D.host.E) := by
        rw [hy₂, (sigR (Af D.host.F) D.sp.cm.sig).map_mul, sigR_tmul_one, ← mul_assoc, ← hy₁r]
      calc finPart D Y = (y₂ : Af D.host.F ⊗[D.host.F] D.host.E) := hYF
        _ = zf * sigR (Af D.host.F) D.sp.cm.sig (y₂ : Af D.host.F ⊗[D.host.F] D.host.E) := e2
        _ = finPart D (matHom V u).1.det * sigR (Af D.host.F) D.sp.cm.sig (finPart D Y) := by
          rw [hzf, ← finPart_det, hYF]
        _ = finPart D (matHom V u).1.det * finPart D (sigR (AF D.host.F) D.sp.cm.sig Y) :=
          congrArg (finPart D (matHom V u).1.det * ·) (finPart_sigR _).symm
        _ = finPart D ((matHom V u).1.det * sigR (AF D.host.F) D.sp.cm.sig Y) := ((finPart D).map_mul _ _).symm
  · have h1 : δc Yf = 1 := by
      refine GlobalTheory.tame_heckeChar_eq_one_of_finUnit D δc δ hc ht pd hunr Yf ⟨?_, ?_, ?_⟩ ⟨w₂, hw₂, by rw [hYf2]; exact hy₂c⟩
      · rw [hYf1]; rfl
      · rw [hYf2]; exact hy₂i
      · have hU : Units.map (finPart D).toMonoidHom Yf = y₂ := Units.ext hYf2
        have e : finPart D ((Yf⁻¹ : (AE D)ˣ) : AE D) = ((y₂⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : _) := by
          rw [← hU, ← MonoidHom.map_inv]
          rfl
        rw [e]; exact hy₂i'
    have h2 : δc Yi = 1 := char_arch_one hc hn ho Yi (by rw [hYi2]; rfl)
    rw [map_mul, h1, h2, mul_one]

theorem dd_mul_right : ∀ (D : D7) (V : HSp D) (M pd : ℕ) (k : Type) [Field k] (σ : k →+* ℂ) (δ : Formalism.L2.Host.HChar D.host.E) (δc : (AE D)ˣ →* Circle), IsAuxiliarySplitSquarefreeLevel D M pd → IsTwist pd σ δ δc → ∀ dd : GA D V → ℂ, (MuVal V δc dd ∨ MuVal V δc⁻¹ dd) → ∀ u : GA D V, Formalism.L2.Pj.gLat V u = ↑(Formalism.L2.Pj.latHat V) → GlobalTheory.Member.FinCong V (M * pd) u → ∀ h : GA D V, dd (h * u) = dd h := by
  intro D V M pd k _ σ δ δc hA hT dd hdd u _ hu h
  have main : ∀ χ : (AE D)ˣ →* Circle, MuVal V χ dd → (∀ y, δc y = 1 → χ y = 1) → dd (h * u) = dd h := by
    intro χ hχ hχδ
    obtain ⟨x, hx⟩ := hχ.1 h
    obtain ⟨y₀, hy₀⟩ := hχ.1 u
    obtain ⟨y, hy, hy1⟩ := exists_root_one hA hT hu y₀ hy₀
    rw [hχ.2 _ _ (isDetRoot_mul hx hy), hχ.2 h x hx, map_mul, hχδ y hy1, mul_one]
  rcases hdd with hd | hd
  · exact main δc hd fun y hy => hy
  · exact main δc⁻¹ hd fun y hy => by rw [MonoidHom.inv_apply, hy, inv_one]

end GlobalTheory.TwistRat.Right
