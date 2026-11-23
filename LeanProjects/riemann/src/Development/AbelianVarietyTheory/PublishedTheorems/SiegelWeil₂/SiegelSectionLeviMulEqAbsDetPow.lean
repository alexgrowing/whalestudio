import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinResidue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDecompositionWittIsotropicStabilize
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionAdeleRealComponentsCmType
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsParamFunOne
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SphericalSectionOfMemCompact

noncomputable section

open scoped Matrix NNReal TensorProduct Classical ComplexOrder
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RegSch

namespace GlobalTheory.Published.SiegelSectionIwasawa

variable {D : D7}

def relat (V : HSp D) (l : Lvl V) (hl : l.Good) : HSp D :=
  { V with
    L0 := l.L.comap (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E))
    standardTuple_isLattice := by
      have e : l.L.comap (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E)) =
          l.L.map (V.frame.equivFun.symm.toLinearMap.restrictScalars (𝓞 D.host.E)) := by
        ext x
        constructor
        · intro hx; exact ⟨_, hx, V.frame.equivFun.symm_apply_apply x⟩
        · rintro ⟨y, hy, rfl⟩
          change V.frame.equivFun (V.frame.equivFun.symm y) ∈ l.L
          rwa [LinearEquiv.apply_symm_apply]
      rw [e]
      refine ⟨hl.1.fg.map _, ?_⟩
      change Submodule.span D.host.E (V.frame.equivFun.symm.toLinearMap '' (l.L : Set _)) = ⊤
      rw [← Submodule.map_span, hl.1.span_eq_top, Submodule.map_top, LinearEquiv.range]
    baseLattice_isUnimodular := by
      have h := (SelfDual.forall_isSelfDualAt_iff (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).ne_zero hl.1).1 hl.2.1
      have e : ∀ x y, hE D.sp.cm.sig V.gram (V.frame.equivFun x) (V.frame.equivFun y) = V.hT x y := fun x y => by
        rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord]
        simp only [← Module.Basis.equivFun_apply]
        rfl
      ext z
      have h2 : z ∈ Formalism.HermitianLatticesTheory.dual V.hT (l.L.comap (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E))) ↔
          ∀ x ∈ l.L.comap (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E)),
            V.hT x z ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
        simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual]
      refine h2.trans (Iff.trans ?_ (h (V.frame.equivFun z)).symm)
      constructor
      · intro H x hx
        obtain ⟨x, rfl⟩ := V.frame.equivFun.surjective x
        rw [e]
        exact Submodule.mem_one.1 (H x hx)
      · intro H x hx
        rw [← e]
        exact Submodule.mem_one.2 (H _ hx) }

theorem frameLat_relat (V : HSp D) (l : Lvl V) (hl : l.Good) : frameLat (relat V l hl) = l.L := by
  ext y
  exact iff_of_eq (congrArg (· ∈ l.L) (V.frame.equivFun.apply_symm_apply y))

theorem hasIw_of_good {V V₀ : HSp D} {r : ℕ} (d : HypDec V V₀ r) (l : Lvl V) (hl : l.Good) : HasIw d l.K := by
  let d' : HypDec (relat V l hl) V₀ r := ⟨d.e, d.e', d.i₀, d.ee, d.e'e', d.e'e, d.iso, d.i₀e, d.i₀e', d.rank_add⟩
  have h := GlobalTheory.Core.Rk.IwAd.hasIw_Kmax D (relat V l hl) V₀ r d' l.c GlobalTheory.Core.Rk.IP.Model.isSplit_two hl.2.2
  intro g
  obtain ⟨q, k, hk, e⟩ := h g
  have e2 : (Kmax (relat V l hl) l.c : Subgroup (GA D V)) = l.K :=
    congrArg (fun L => levelAll D.sp.cm.sig V.gram L l.c) (frameLat_relat V l hl)
  exact ⟨⟨q.1, q.2⟩, k, e2 ▸ hk, e⟩

theorem isIwasawa_of_good {V V₀ : HSp D} {r : ℕ} (d : HypDec V V₀ r) (l : Lvl V) (hl : l.Good) :
    IsIwasawa (absDet d) l.K :=
  haveI := hl.1
  isIwasawa_of_isCompact (isClosed_stab d) (continuous_absDet d) (isCompact_levelAll (AdelicU.isCMExt_host D) _ _ _)
    (hasIw_of_good d l hl)

theorem siegel_section_levi_mul_eq_abs_det_pow {V V₀ : HSp D} {r : ℕ} (d : HypDec V V₀ r) (l : Lvl V) (hl : l.Good) (s : ℂ)
    (α : GL (Fin r) (AE D)) {k : GA D V} (hk : k ∈ l.K) :
    sphericalSectionIwasawa d l.K s (d.levi α * k) = npow (absA D (Matrix.GeneralLinearGroup.det α)) (s + rhoH V r) := by
  have := (isIwasawa_of_good d l hl).iwAbs_mul ⟨_, levi_mem d α⟩ hk
  rw [absDet, MonoidHom.comp_apply, MonoidHom.comp_apply, onX_levi] at this
  exact congrArg (npow · _) this

section Arch

variable {m k r : ℕ} {X Y : Matrix (Fin m) (Fin r) ℂ} {Z : Matrix (Fin m) (Fin k) ℂ} {P R : Matrix (Fin r) (Fin m) ℂ}
  {Q : Matrix (Fin k) (Fin m) ℂ} {G : Matrix (Fin m) (Fin m) ℂ} {G₀ s₀ B B' : Matrix (Fin k) (Fin k) ℂ}

theorem cartan_sum (PX : P * X = 1) (PZ : P * Z = 0) (PY : P * Y = 0) (QX : Q * X = 0) (QZ : Q * Z = 1) (QY : Q * Y = 0)
    (RX : R * X = 0) (RZ : R * Z = 0) (RY : R * Y = 1) (hs : X * P + Z * Q + Y * R = 1)
    (hG : G = Rᴴ * P + Qᴴ * (G₀ * Q) + Pᴴ * R) (h₀ : IsCartanInv G₀ s₀) (hB : G₀ * s₀ = Bᴴ * B) (hB' : B' * B = 1) :
    IsCartanInv G (X * R + Z * (s₀ * Q) + Y * P) ∧
      G * (X * R + Z * (s₀ * Q) + Y * P) = Pᴴ * P + Qᴴ * (Bᴴ * B * Q) + Rᴴ * R := by
  have h1 : P * (X * R + Z * (s₀ * Q) + Y * P) = R := by
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, PX, PZ, PY]; simp
  have h2 : Q * (X * R + Z * (s₀ * Q) + Y * P) = s₀ * Q := by
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, QX, QZ, QY]; simp
  have h3 : R * (X * R + Z * (s₀ * Q) + Y * P) = P := by
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, RX, RZ, RY]; simp
  generalize hS : X * R + Z * (s₀ * Q) + Y * P = s at h1 h2 h3
  have h4 : G * s = Pᴴ * P + Qᴴ * (Bᴴ * B * Q) + Rᴴ * R := by
    rw [hG, ← hB]
    simp only [Matrix.add_mul, Matrix.mul_assoc, h1, h2, h3]
    abel
  refine ⟨⟨?_, ?_, ?_⟩, h4⟩
  · conv_lhs => lhs; rw [← hS]
    simp only [Matrix.add_mul, Matrix.mul_assoc, h1, h2, h3]
    rw [← Matrix.mul_assoc s₀, h₀.1, Matrix.one_mul, hs]
  · have e : sᴴ * G * s = (R * s)ᴴ * (P * s) + (Q * s)ᴴ * (G₀ * (Q * s)) + (P * s)ᴴ * (R * s) := by
      rw [hG]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.conjTranspose_mul]
    rw [e, h1, h2, h3, hG, Matrix.conjTranspose_mul, Matrix.mul_assoc Qᴴ, ← Matrix.mul_assoc G₀, ← Matrix.mul_assoc s₀ᴴ,
      ← Matrix.mul_assoc s₀ᴴ, h₀.2.1]
    abel
  · have e : G * s = (Matrix.fromRows (Matrix.fromRows P (B * Q)) R)ᴴ * Matrix.fromRows (Matrix.fromRows P (B * Q)) R := by
      rw [h4]
      simp only [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromRows,
        Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [e]
    have e2 : Matrix.fromCols (Matrix.fromCols X (Z * B')) Y * Matrix.fromRows (Matrix.fromRows P (B * Q)) R = 1 := by
      rw [Matrix.fromCols_mul_fromRows, Matrix.fromCols_mul_fromRows, Matrix.mul_assoc Z, ← Matrix.mul_assoc B', hB',
        Matrix.one_mul, hs]
    refine Matrix.PosDef.conjTranspose_mul_self _ fun x y hxy => ?_
    have := congrArg (Matrix.fromCols (Matrix.fromCols X (Z * B')) Y *ᵥ ·) hxy
    simpa only [Matrix.mulVec_mulVec, e2, Matrix.one_mulVec] using this

theorem form_eq {b b' G s : Matrix (Fin m) (Fin m) ℂ} (hb : b * b' = 1) (hs : b * bᴴ * G = s) (h : s * s = 1) :
    G * s = b'ᴴ * b' := by
  have hb' : b' * b = 1 := mul_eq_one_comm.1 hb
  have e : b'ᴴ * b' * (b * bᴴ * G * s) = G * s := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc b' b, hb', Matrix.one_mul, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hb]
    simp
  rw [← e, hs, h, Matrix.mul_one]

end Arch

section Standard

variable {V V₀ : HSp D} {r : ℕ} (d : HypDec V V₀ r)

theorem exists_frame (l₀ : Lvl V₀) (h₀ : IsMaj V₀ l₀.c) : ∃ c : GL (Fin V.rank) (AE D), IsMaj V c ∧
    ∀ w, (adj (c⁻¹).1 ⬝ (c⁻¹).1 : Mx D V.rank V.rank).map (compInf D.host.F D.host.E w) =
      (adj d.pX ⬝ d.pX + adj d.p0 ⬝ (l₀.form ⬝ d.p0) + adj d.pY ⬝ d.pY : Mx D V.rank V.rank).map
        (compInf D.host.F D.host.E w) := by
  obtain ⟨⟨θ, hθ⟩, -⟩ := GlobalTheory.Ker.exists_infFam_and_stdChar D
  obtain ⟨r1, r2, r3, -⟩ := GlobalTheory.StdUnn.RealComp.real_components D θ hθ
  have cm : ∀ τ {a b c : ℕ} (x : Mx D a b) (y : Mx D b c), compAt θ τ (x ⬝ y) = compAt θ τ x * compAt θ τ y :=
    fun τ _ _ _ x y => Matrix.map_mul (f := (θ τ).comp (infPart D))
  have ca : ∀ τ {a b : ℕ} (x y : Mx D a b), compAt θ τ (x + y) = compAt θ τ x + compAt θ τ y :=
    fun τ _ _ x y => Matrix.map_add ((θ τ).comp (infPart D)) (map_add _) x y
  have c0 : ∀ τ {a b : ℕ}, compAt θ τ (0 : Mx D a b) = 0 :=
    fun τ _ _ => Matrix.map_zero ((θ τ).comp (infPart D)) (map_zero _)
  have c1 : ∀ τ {a : ℕ}, compAt θ τ (1 : Mx D a a) = 1 :=
    fun τ _ => Matrix.map_one ((θ τ).comp (infPart D)) (map_zero _) (map_one _)
  have cj : ∀ τ {a b : ℕ} (x : Mx D a b), compAt θ τ (adj x) = (compAt θ τ x)ᴴ :=
    fun τ _ _ x => Matrix.ext fun i j => r2 _ τ
  have cg : ∀ τ (S : HSp D), compAt θ τ (gA S) = gramAt D S τ := fun τ S => Matrix.ext fun i j => r3 _ τ
  have z : ∀ τ {a b c : ℕ} {x : Mx D a b} {y : Mx D b c}, x ⬝ y = 0 → compAt θ τ x * compAt θ τ y = 0 :=
    fun τ _ _ _ x y h => by rw [← cm, h, c0]
  have o : ∀ τ {a b : ℕ} {x : Mx D a b} {y : Mx D b a}, x ⬝ y = 1 → compAt θ τ x * compAt θ τ y = 1 :=
    fun τ _ _ x y h => by rw [← cm, h, c1]
  have key := fun τ => cartan_sum (G := gramAt D V τ) (B := compAt θ τ (l₀.c⁻¹).1) (B' := compAt θ τ l₀.c.1)
    (o τ d.pX_jX) (z τ d.pX_j0) (z τ d.pX_jY) (z τ d.p0_jX) (o τ d.p0_j0) (z τ d.p0_jY) (z τ d.pY_jX) (z τ d.pY_j0)
    (o τ d.pY_jY) (by rw [← cm, ← cm, ← cm, ← ca, ← ca, d.sum_eq_one, c1])
    (by rw [← cg, d.gA_eq]; simp only [ca, cm, cj, cg]) (h₀.isCartanInv hθ τ)
    (form_eq (compAt_mul_inv τ l₀.c) rfl (h₀.isCartanInv hθ τ).1) (compAt_mul_inv τ l₀.c)
  obtain ⟨c, hc, -, hs⟩ := exists_isMaj_frameInv_eq hθ fun τ => (key τ).1
  refine ⟨c, hc, fun w => ?_⟩
  have e : ∀ τ, compAt θ τ (adj (c⁻¹).1 ⬝ (c⁻¹).1 : Mx D V.rank V.rank) =
      compAt θ τ (adj d.pX ⬝ d.pX + adj d.p0 ⬝ (l₀.form ⬝ d.p0) + adj d.pY ⬝ d.pY : Mx D V.rank V.rank) := fun τ => by
    have h1 := form_eq (compAt_mul_inv τ c) (hs τ) (key τ).1.1
    rw [cm, cj, ← h1, (key τ).2]
    simp only [Lvl.form, ca, cm, cj]
  ext i j
  refine sub_eq_zero.1 ((map_sub (compInf D.host.F D.host.E w) _ _).symm.trans ((r1 _).2 (fun τ => ?_) w))
  rw [map_sub, map_sub]
  exact sub_eq_zero.2 (congrFun (congrFun (e τ) i) j)

def lat (L₀ : Submodule (𝓞 D.host.E) (Fin V₀.rank → D.host.E)) : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
  (stdLattice D.host.E r).comap (d.qX.mulVecLin.restrictScalars _) ⊓ L₀.comap (d.q0.mulVecLin.restrictScalars _) ⊓
    (stdLattice D.host.E r).comap (d.qY.mulVecLin.restrictScalars _)

theorem mem_lat {L₀ : Submodule (𝓞 D.host.E) (Fin V₀.rank → D.host.E)} {z : Fin V.rank → D.host.E} : z ∈ lat d L₀ ↔
    (d.qX *ᵥ z ∈ stdLattice D.host.E r ∧ d.q0 *ᵥ z ∈ L₀ ∧ d.qY *ᵥ z ∈ stdLattice D.host.E r) := and_assoc

theorem rat_zero_of {a b c : ℕ} {x : Matrix (Fin a) (Fin b) D.host.E} {y : Matrix (Fin b) (Fin c) D.host.E}
    (h : (rat x ⬝ rat y : Mx D a c) = 0) : x * y = 0 := rat_injective (by rw [rat_mul, h, rat_zero])

theorem rat_one_of {a b : ℕ} {x : Matrix (Fin a) (Fin b) D.host.E} {y : Matrix (Fin b) (Fin a) D.host.E}
    (h : (rat x ⬝ rat y : Mx D a a) = 1) : x * y = 1 := rat_injective (by rw [rat_mul, h, rat_one])

variable {L₀ : Submodule (𝓞 D.host.E) (Fin V₀.rank → D.host.E)}

theorem e_mem {x : Fin r → D.host.E} (h : x ∈ stdLattice D.host.E r) : d.e *ᵥ x ∈ lat d L₀ := by
  rw [mem_lat, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, rat_one_of (x := d.qX) (y := d.e) d.pX_jX, rat_zero_of (x := d.q0) (y := d.e) d.p0_jX,
    rat_zero_of (x := d.qY) (y := d.e) d.pY_jX, Matrix.one_mulVec, Matrix.zero_mulVec, Matrix.zero_mulVec]
  exact ⟨h, zero_mem _, zero_mem _⟩

theorem i_mem {x : Fin V₀.rank → D.host.E} (h : x ∈ L₀) : d.i₀ *ᵥ x ∈ lat d L₀ := by
  rw [mem_lat, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, rat_zero_of (x := d.qX) (y := d.i₀) d.pX_j0, rat_one_of (x := d.q0) (y := d.i₀) d.p0_j0,
    rat_zero_of (x := d.qY) (y := d.i₀) d.pY_j0, Matrix.one_mulVec, Matrix.zero_mulVec]
  exact ⟨zero_mem _, h, zero_mem _⟩

theorem e'_mem {x : Fin r → D.host.E} (h : x ∈ stdLattice D.host.E r) : d.e' *ᵥ x ∈ lat d L₀ := by
  rw [mem_lat, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, rat_zero_of (x := d.qX) (y := d.e') d.pX_jY, rat_zero_of (x := d.q0) (y := d.e') d.p0_jY,
    rat_one_of (x := d.qY) (y := d.e') d.pY_jY, Matrix.one_mulVec, Matrix.zero_mulVec, Matrix.zero_mulVec]
  exact ⟨zero_mem _, zero_mem _, h⟩

theorem decomp (z : Fin V.rank → D.host.E) : z = d.e *ᵥ (d.qX *ᵥ z) + d.i₀ *ᵥ (d.q0 *ᵥ z) + d.e' *ᵥ (d.qY *ᵥ z) := by
  simp only [Matrix.mulVec_mulVec, ← Matrix.add_mulVec, d.sum_eq_one_rat, Matrix.one_mulVec]

theorem mem_span_of {a b : ℕ} (A : Matrix (Fin a) (Fin b) D.host.E) {M : Submodule (𝓞 D.host.E) (Fin b → D.host.E)}
    {L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} (hM : Submodule.IsLattice D.host.E M) (h : ∀ x ∈ M, A *ᵥ x ∈ L)
    (x : Fin b → D.host.E) : A *ᵥ x ∈ Submodule.span D.host.E (L : Set (Fin a → D.host.E)) := by
  have : Submodule.span D.host.E (M : Set (Fin b → D.host.E)) ≤
      (Submodule.span D.host.E (L : Set (Fin a → D.host.E))).comap A.mulVecLin :=
    Submodule.span_le.2 fun x hx => Submodule.subset_span (h x hx)
  exact this (hM.span_eq_top ▸ Submodule.mem_top)

theorem isLattice_lat (h : Submodule.IsLattice D.host.E L₀) : Submodule.IsLattice D.host.E (lat d L₀) := by
  have hs : Submodule.IsLattice D.host.E (stdLattice D.host.E r) := isLattice_stdLattice ..
  constructor
  · have e : lat d L₀ = (stdLattice D.host.E r).map (d.e.mulVecLin.restrictScalars _) ⊔
        L₀.map (d.i₀.mulVecLin.restrictScalars _) ⊔ (stdLattice D.host.E r).map (d.e'.mulVecLin.restrictScalars _) := by
      refine le_antisymm (fun z hz => ?_) (sup_le (sup_le ?_ ?_) ?_)
      · obtain ⟨h1, h2, h3⟩ := (mem_lat d).1 hz
        rw [decomp d z]
        exact Submodule.add_mem_sup (Submodule.add_mem_sup ⟨_, h1, rfl⟩ ⟨_, h2, rfl⟩) ⟨_, h3, rfl⟩
      · rintro _ ⟨x, hx, rfl⟩; exact e_mem d hx
      · rintro _ ⟨x, hx, rfl⟩; exact i_mem d hx
      · rintro _ ⟨x, hx, rfl⟩; exact e'_mem d hx
    rw [e]
    exact ((hs.fg.map _).sup (h.fg.map _)).sup (hs.fg.map _)
  · refine eq_top_iff.2 fun z _ => ?_
    rw [decomp d z]
    exact add_mem (add_mem (mem_span_of _ hs (fun _ => e_mem d) _) (mem_span_of _ h (fun _ => i_mem d) _))
      (mem_span_of _ hs (fun _ => e'_mem d) _)

theorem hE_eq {a : ℕ} (J : Matrix (Fin a) (Fin a) D.host.E) (x y : Fin a → D.host.E) :
    hE D.sp.cm.sig J x y = star x ⬝ᵥ J *ᵥ y := by
  simp only [hE, Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rfl

theorem hE_split (x y : Fin V.rank → D.host.E) : hE D.sp.cm.sig V.gram x y =
    hE D.sp.cm.sig 1 (d.qY *ᵥ x) (d.qX *ᵥ y) + hE D.sp.cm.sig V₀.gram (d.q0 *ᵥ x) (d.q0 *ᵥ y) +
      hE D.sp.cm.sig 1 (d.qX *ᵥ x) (d.qY *ᵥ y) := by
  have e : V.gram = d.qYᴴ * d.qX + d.q0ᴴ * (V₀.gram * d.q0) + d.qXᴴ * d.qY := rat_injective (by
    simp only [rat_add, rat_mul, rat_conjTranspose]
    exact d.gA_eq)
  simp only [hE_eq, Matrix.one_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← dotProduct_add, ← Matrix.add_mulVec, Matrix.one_mul]
  rw [← e]

theorem selfDual_lat (h : Submodule.IsLattice D.host.E L₀) (h' : ∀ v, IsSelfDualAt D.sp.cm.sig V₀.gram L₀ v) :
    ∀ v, IsSelfDualAt D.sp.cm.sig V.gram (lat d L₀) v := by
  have hs : Submodule.IsLattice D.host.E (stdLattice D.host.E r) := isLattice_stdLattice ..
  have a0 := (SelfDual.forall_isSelfDualAt_iff (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V₀).ne_zero h).1 h'
  have a1 := (SelfDual.forall_isSelfDualAt_iff (σ := D.sp.cm.sig) (J := 1) (by simp) hs).1
    (isSelfDualAt_stdLattice_one _)
  have z : ∀ {a : ℕ} (J : Matrix (Fin a) (Fin a) D.host.E) y, hE D.sp.cm.sig J 0 y = 0 := fun J y => by
    rw [hE_eq, star_zero, zero_dotProduct]
  refine (SelfDual.forall_isSelfDualAt_iff (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V).ne_zero (isLattice_lat d h)).2 fun y =>
    ⟨fun hy x hx => ?_, fun H => (mem_lat d).2 ⟨(a1 _).2 fun x hx => ?_, (a0 _).2 fun x hx => ?_, (a1 _).2 fun x hx => ?_⟩⟩
  · obtain ⟨x1, x2, x3⟩ := (mem_lat d).1 hx
    obtain ⟨y1, y2, y3⟩ := (mem_lat d).1 hy
    rw [hE_split d]
    exact add_mem (add_mem ((a1 _).1 y1 _ x3) ((a0 _).1 y2 _ x2)) ((a1 _).1 y3 _ x1)
  · have := H _ (e'_mem d hx)
    simpa only [hE_split d, Matrix.mulVec_mulVec x d.qX d.e', Matrix.mulVec_mulVec x d.q0 d.e', Matrix.mulVec_mulVec x d.qY d.e',
      rat_zero_of (x := d.qX) (y := d.e') d.pX_jY, rat_zero_of (x := d.q0) (y := d.e') d.p0_jY, rat_one_of (x := d.qY) (y := d.e') d.pY_jY, Matrix.one_mulVec, Matrix.zero_mulVec, z, add_zero] using this
  · have := H _ (i_mem d hx)
    simpa only [hE_split d, Matrix.mulVec_mulVec x d.qX d.i₀, Matrix.mulVec_mulVec x d.q0 d.i₀, Matrix.mulVec_mulVec x d.qY d.i₀,
      rat_zero_of (x := d.qX) (y := d.i₀) d.pX_j0, rat_one_of (x := d.q0) (y := d.i₀) d.p0_j0, rat_zero_of (x := d.qY) (y := d.i₀) d.pY_j0, Matrix.one_mulVec, Matrix.zero_mulVec, z, add_zero,
      zero_add] using this
  · have := H _ (e_mem d hx)
    simpa only [hE_split d, Matrix.mulVec_mulVec x d.qX d.e, Matrix.mulVec_mulVec x d.q0 d.e, Matrix.mulVec_mulVec x d.qY d.e,
      rat_one_of (x := d.qX) (y := d.e) d.pX_jX, rat_zero_of (x := d.q0) (y := d.e) d.p0_jX, rat_zero_of (x := d.qY) (y := d.e) d.pY_jX, Matrix.one_mulVec, Matrix.zero_mulVec, z, add_zero,
      zero_add] using this

theorem exists_levels : ∃ (l : Lvl V) (l₀ : Lvl V₀), l.Good ∧ l₀.Good ∧ Compat d l l₀ ∧ HasIw d l.K := by
  obtain ⟨a, ha⟩ := exists_isMaj V₀
  have h₀ : (⟨frameLat V₀, a⟩ : Lvl V₀).Good := ⟨isLattice_frameLat_host V₀, SelfDual.isSelfDualAt_frameLat D V₀, ha⟩
  obtain ⟨c, hc, e⟩ := exists_frame d ⟨frameLat V₀, a⟩ ha
  have h : (⟨lat d (frameLat V₀), c⟩ : Lvl V).Good := ⟨isLattice_lat d h₀.1, selfDual_lat d h₀.1 h₀.2.1, hc⟩
  exact ⟨_, _, h, h₀, ⟨fun _ => mem_lat d, e⟩, hasIw_of_good d _ h⟩

end Standard

theorem hypotheses (D : D7) : ∃ (V V₀ : HSp D) (r : ℕ) (d : HypDec V V₀ r) (l : Lvl V) (l₀ : Lvl V₀),
    IsAniso V₀ ∧ 0 < r ∧ l.Good ∧ l₀.Good ∧ Compat d l l₀ ∧ HasIw d l.K ∧ rhoH V r = 1 / 2 := by
  obtain ⟨l, l₀, h⟩ := exists_levels (GlobalTheory.RegSW.Model.hypTwo D)
  refine ⟨_, _, 1, _, l, l₀, GlobalTheory.RegSW.Model.isAniso_zero D, Nat.one_pos, h.1, h.2.1, h.2.2.1, h.2.2.2, ?_⟩
  show ((2 : ℕ) - (1 : ℕ) : ℝ) / 2 = 1 / 2
  norm_num

end GlobalTheory.Published.SiegelSectionIwasawa

end
