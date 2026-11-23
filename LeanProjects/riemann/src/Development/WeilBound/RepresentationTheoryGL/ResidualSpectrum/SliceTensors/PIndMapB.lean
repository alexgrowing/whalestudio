import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermLeviParabolicFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAuxiliaryStatementA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipLevIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericFiniteByInduction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin
open scoped ContDiff

namespace PositivityTheory.Rg.Rs.InducedTensorMap

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

namespace B

variable {R : Type} [CommRing R]

theorem lev_cc (m : GL (Fin r) R × GL (Fin s) R) (i j : Fin r) :
    (lev R r s m : Matrix (Fin (r + s)) (Fin (r + s)) R) (Fin.castAdd s i) (Fin.castAdd s j) = (m.1 : Matrix _ _ R) i j := by
  simp [GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.stdSum]

theorem lev_nn (m : GL (Fin r) R × GL (Fin s) R) (i j : Fin s) :
    (lev R r s m : Matrix (Fin (r + s)) (Fin (r + s)) R) (Fin.natAdd r i) (Fin.natAdd r j) = (m.2 : Matrix _ _ R) i j := by
  simp [GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.stdSum]

theorem lev_cn (m : GL (Fin r) R × GL (Fin s) R) (i : Fin r) (j : Fin s) :
    (lev R r s m : Matrix (Fin (r + s)) (Fin (r + s)) R) (Fin.castAdd s i) (Fin.natAdd r j) = 0 := by
  simp [GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.stdSum]

theorem lev_nc (m : GL (Fin r) R × GL (Fin s) R) (i : Fin s) (j : Fin r) :
    (lev R r s m : Matrix (Fin (r + s)) (Fin (r + s)) R) (Fin.natAdd r i) (Fin.castAdd s j) = 0 := by
  simp [GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.stdSum]

theorem unip_col (x : BlockIx (r + s) r → R) (i : Fin (r + s)) (k : Fin r) :
    ((unip x : GL (Fin (r + s)) R) : Matrix _ _ R) i (Fin.castAdd s k) =
      (1 : Matrix (Fin (r + s)) (Fin (r + s)) R) i (Fin.castAdd s k) := by
  have := k.isLt
  rw [GlobalTheory.CompanionTheory.AffglAssembly.unip_eq_unipGL, GroundTheory.Automorphic.AutomorphicForm.coe_unipGL,
    GroundTheory.Automorphic.AutomorphicForm.unipMatrix, Matrix.add_apply, GroundTheory.Automorphic.AutomorphicForm.blockEntry_apply,
    dif_neg (fun h => by have := h.2; simp only [Fin.val_castAdd] at this; omega), add_zero]

theorem unip_row (x : BlockIx (r + s) r → R) (k : Fin s) (j : Fin (r + s)) :
    ((unip x : GL (Fin (r + s)) R) : Matrix _ _ R) (Fin.natAdd r k) j =
      (1 : Matrix (Fin (r + s)) (Fin (r + s)) R) (Fin.natAdd r k) j := by
  rw [GlobalTheory.CompanionTheory.AffglAssembly.unip_eq_unipGL, GroundTheory.Automorphic.AutomorphicForm.coe_unipGL,
    GroundTheory.Automorphic.AutomorphicForm.unipMatrix, Matrix.add_apply, GroundTheory.Automorphic.AutomorphicForm.blockEntry_apply,
    dif_neg (fun h => by have := h.1; simp only [Fin.val_natAdd] at this; omega), add_zero]

end B

open B

theorem unip_zero {R : Type} [CommRing R] {a r : ℕ} : unip (0 : BlockIx a r → R) = 1 := by
  rw [GlobalTheory.CompanionTheory.AffglAssembly.unip_eq_unipGL]
  exact GroundTheory.Automorphic.AutomorphicForm.unipGL_zero

theorem unip_lev_ll {R : Type} [CommRing R] (u : BlockIx (r + s) r → R) (m : GL (Fin r) R × GL (Fin s) R)
    (i : Fin s) (j : Fin r) :
    ((unip u * lev R r s m : GL (Fin (r + s)) R) : Matrix _ _ R) (Fin.natAdd r i) (Fin.castAdd s j) = 0 := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_add]
  have h : ∀ x : Fin r, Fin.natAdd r i ≠ Fin.castAdd s x := fun x h => by
    have := congrArg Fin.val h
    have := x.isLt
    simp only [Fin.val_natAdd, Fin.val_castAdd] at *
    omega
  simp [unip_row, lev_nc, lev_cc, Matrix.one_apply, h]

theorem unip_lev_cc {R : Type} [CommRing R] (u : BlockIx (r + s) r → R) (m : GL (Fin r) R × GL (Fin s) R)
    (i j : Fin r) :
    ((unip u * lev R r s m : GL (Fin (r + s)) R) : Matrix _ _ R) (Fin.castAdd s i) (Fin.castAdd s j) =
      (m.1 : Matrix _ _ R) i j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_add]
  simp [unip_col, lev_nc, lev_cc, Matrix.one_apply]

theorem unip_lev_nn {R : Type} [CommRing R] (u : BlockIx (r + s) r → R) (m : GL (Fin r) R × GL (Fin s) R)
    (i j : Fin s) :
    ((unip u * lev R r s m : GL (Fin (r + s)) R) : Matrix _ _ R) (Fin.natAdd r i) (Fin.natAdd r j) =
      (m.2 : Matrix _ _ R) i j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_add]
  simp [unip_row, lev_cn, lev_nn, Matrix.one_apply]

theorem lev_mul_unip {R : Type} [CommRing R] (m : GL (Fin r) R × GL (Fin s) R) (u : BlockIx (r + s) r → R) :
    ∃ v : BlockIx (r + s) r → R, lev R r s m * unip u = unip v * lev R r s m := by
  have h1 := GlobalTheory.CompanionTheory.CTFin.blockDiag_lev (R := R) m
  have h2 : GlobalTheory.CompanionTheory.CTFin.BlockDiag r ((lev R r s m)⁻¹).val := by
    rw [← map_inv]; exact GlobalTheory.CompanionTheory.CTFin.blockDiag_lev _
  refine ⟨(GlobalTheory.CompanionTheory.CTFin.conjE (lev R r s m) h1 h2).symm u, ?_⟩
  rw [GlobalTheory.CompanionTheory.CTFin.unip_mul_eq _ h1 h2, AddEquiv.apply_symm_apply]

theorem cf_mul (a : ℕ) (k k' : Kinf E a) (g g' : GL (Fin a) (Af E)) : cf a k g * cf a k' g' = cf a (k * k') (g * g') := by
  refine ga_ext ?_ ?_ <;> simp [cf]

theorem exists_decomp (x : GA E (r + s)) : ∃ (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s))
    (g : GL (Fin (r + s)) (Af E)), x = unip u * lev (Ad E) r s m * cf (r + s) k g := by
  obtain ⟨T, hT⟩ := GlobalTheory.CompanionTheory.CTFin.IwaAd.iwasawa_finite_cosets E r s ⊤ isOpen_univ
  obtain ⟨y, m, t, k, l, -, -, rfl⟩ := hT x
  refine ⟨y, m, k, t * l, ?_⟩
  rw [cf, map_mul, ← mul_assoc (infGL E (r + s) _), infGL_comm]
  simp only [mul_assoc]

theorem levi_cf {u : BlockIx (r + s) r → Ad E} {m : GA E r × GA E s} {k : Kinf E (r + s)} {g : GL (Fin (r + s)) (Af E)}
    (h : unip u * lev (Ad E) r s m = cf (r + s) k g) :
    ∃ (k₁ : Kinf E r) (g₁ : GL (Fin r) (Af E)) (k₂ : Kinf E s) (g₂ : GL (Fin s) (Af E)), m = (cf r k₁ g₁, cf s k₂ g₂) := by
  have h1 := congrArg (Matrix.GeneralLinearGroup.map (pInf E)) h
  rw [map_mul, GlobalTheory.CompanionTheory.CTFin.IwaAd.map_unip, GlobalTheory.CompanionTheory.CTFin.IwaAd.map_lev, cf, map_mul, pInf_infGL, pInf_finGL, mul_one] at h1
  set y₁ := Matrix.GeneralLinearGroup.map (pInf E) m.1 with hy₁
  set y₂ := Matrix.GeneralLinearGroup.map (pInf E) m.2 with hy₂
  have hv : ((Unitary.toUnits k : GL (Fin (r + s)) (Cinf E)) : Matrix _ _ _) = k.1 := rfl
  have hll : ∀ i j, k.1 (Fin.natAdd r i) (Fin.castAdd s j) = 0 := fun i j => by rw [← hv, ← h1, unip_lev_ll]
  have hcc : ∀ i j, k.1 (Fin.castAdd s i) (Fin.castAdd s j) = y₁.val i j := fun i j => by rw [← hv, ← h1, unip_lev_cc]
  have hnn : ∀ i j, k.1 (Fin.natAdd r i) (Fin.natAdd r j) = y₂.val i j := fun i j => by rw [← hv, ← h1, unip_lev_nn]
  have u₁ : y₁.val ∈ Matrix.unitaryGroup (Fin r) (Cinf E) := by
    rw [Matrix.mem_unitaryGroup_iff']
    ext1 i j
    have := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 k.2) (Fin.castAdd s i)) (Fin.castAdd s j)
    rw [Matrix.mul_apply, Fin.sum_univ_add] at this
    simp only [Matrix.star_apply, hll, hcc, mul_zero, Finset.sum_const_zero, add_zero, Matrix.one_apply,
      Fin.castAdd_inj] at this
    rw [Matrix.mul_apply, Matrix.one_apply, ← this]
    rfl
  have u₂ : y₂.val ∈ Matrix.unitaryGroup (Fin s) (Cinf E) := by
    rw [Matrix.mem_unitaryGroup_iff]
    ext1 i j
    have := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.1 k.2) (Fin.natAdd r i)) (Fin.natAdd r j)
    rw [Matrix.mul_apply, Fin.sum_univ_add] at this
    simp only [Matrix.star_apply, hll, hnn, zero_mul, Finset.sum_const_zero, zero_add, Matrix.one_apply,
      Fin.natAdd_inj] at this
    rw [Matrix.mul_apply, Matrix.one_apply, ← this]
    rfl
  refine ⟨⟨_, u₁⟩, Matrix.GeneralLinearGroup.map (pFin E) m.1, ⟨_, u₂⟩, Matrix.GeneralLinearGroup.map (pFin E) m.2,
    Prod.ext ?_ ?_⟩
  · exact (infGL_mul_finGL m.1).symm.trans (congrArg (fun z => infGL E r z * _) (Units.ext rfl))
  · exact (infGL_mul_finGL m.2).symm.trans (congrArg (fun z => infGL E s z * _) (Units.ext rfl))

theorem lev_mul_infGL (m : GA E r × GA E s) (u : BlockIx (r + s) r → Cinf E) (b₁ : GL (Fin r) (Cinf E))
    (b₂ : GL (Fin s) (Cinf E)) (κ : Kinf E (r + s)) :
    ∃ v : BlockIx (r + s) r → Ad E, lev (Ad E) r s m * infGL E (r + s) (unip u * lev (Cinf E) r s (b₁, b₂) * Unitary.toUnits κ) =
      unip v * lev (Ad E) r s (m.1 * infGL E r b₁, m.2 * infGL E s b₂) * cf (r + s) κ 1 := by
  have e : infGL E (r + s) (unip u) = unip fun p => sInf E (u p) := by
    refine ga_ext ?_ ?_
    · rw [pInf_infGL, GlobalTheory.CompanionTheory.CTFin.IwaAd.map_unip]
      congr 1
      funext p
      exact ((infEq E).symm_apply_apply _).symm
    · rw [pFin_infGL, GlobalTheory.CompanionTheory.CTFin.IwaAd.map_unip]
      exact unip_zero.symm
  obtain ⟨v, hv⟩ := lev_mul_unip m fun p => sInf E (u p)
  refine ⟨v, ?_⟩
  rw [map_mul, map_mul, e, ← GlobalTheory.CompanionTheory.CTFin.Slice1.lev_infGL, ← mul_assoc, ← mul_assoc, hv, cf, map_one, mul_one, mul_assoc (unip v),
    ← map_mul]
  rfl

end PositivityTheory.Rg.Rs.InducedTensorMap

end
