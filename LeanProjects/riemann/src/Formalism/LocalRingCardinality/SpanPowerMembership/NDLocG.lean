import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocF

noncomputable section

namespace Formalism.BasicNotions.Examples₂.LB

open NumberField IsDedekindDomain Polynomial IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {l : ℕ} [hl : Fact l.Prime]

section Emb

variable {F : Type} [Field F] [NumberField F]

def Kphi (φ : F →+* PadicAlgCl l) : IntermediateField ℚ_[l] (PadicAlgCl l) :=
  IntermediateField.adjoin ℚ_[l] (Set.range fun i => φ (Module.finBasis ℚ F i))

instance Kphi_fin (φ : F →+* PadicAlgCl l) : FiniteDimensional ℚ_[l] (Kphi φ) :=
  IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

theorem phi_mem (φ : F →+* PadicAlgCl l) (x : F) : φ x ∈ Kphi φ := by
  have hx := (Module.finBasis ℚ F).sum_repr x
  rw [← hx, map_sum]
  refine sum_mem (fun i _ => ?_)
  rw [map_rat_smul, Rat.smul_def]
  refine mul_mem ?_ (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  first
  | exact SubfieldClass.ratCast_mem _ _
  | exact ratCast_mem _ _
  | exact (Kphi φ).toSubfield.ratCast_mem _
  | simp

variable (F l) in

def KE : IntermediateField ℚ_[l] (PadicAlgCl l) := ⨆ φ : F →+* PadicAlgCl l, Kphi φ

instance KE_fin : FiniteDimensional ℚ_[l] (KE l F) :=
  IntermediateField.finiteDimensional_iSup_of_finite

theorem phi_mem_KE (φ : F →+* PadicAlgCl l) (x : F) : φ x ∈ KE l F := (le_iSup (fun ψ : F →+* PadicAlgCl l => Kphi ψ) φ) (phi_mem φ x)

theorem conj_mem_KE (φ : F →+* PadicAlgCl l) (τ : ↥(Kphi φ) →ₐ[ℚ_[l]] PadicAlgCl l) (y : ↥(Kphi φ)) :
    τ y ∈ KE l F := by
  let ψ : F →+* PadicAlgCl l := τ.toRingHom.comp (φ.codRestrict (Kphi φ) (phi_mem φ))
  have hle : Kphi φ ≤ ((Kphi ψ).comap τ).map (Kphi φ).val := by
    show IntermediateField.adjoin ℚ_[l] _ ≤ _
    rw [IntermediateField.adjoin_le_iff]
    rintro s ⟨i, rfl⟩
    first
    | exact ⟨⟨φ (Module.finBasis ℚ F i), phi_mem φ _⟩, phi_mem ψ (Module.finBasis ℚ F i), rfl⟩
    | exact IntermediateField.mem_map.mpr
        ⟨⟨φ (Module.finBasis ℚ F i), phi_mem φ _⟩, phi_mem ψ (Module.finBasis ℚ F i), rfl⟩
  obtain ⟨z, hz, hzy⟩ := hle y.2
  have hzy' : z = y := Subtype.ext hzy
  have key : τ y ∈ Kphi ψ := by
    rw [← hzy']
    exact hz
  exact (le_iSup (fun ψ' : F →+* PadicAlgCl l => Kphi ψ') ψ) key

theorem exists_embAt (w : HeightOneSpectrum (𝓞 F)) (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) :
    ∃ φ : F →+* PadicAlgCl l, ∀ x : 𝓞 F, x ∈ w.asIdeal ↔ ‖φ (x : F)‖ < 1 := by
  have hA := isPlaceOver_placeOf (AlgebraicClosure F) w
  have hAl : (placeOf (AlgebraicClosure F) w).valuation ((l : ℕ) : AlgebraicClosure F) < 1 := by
    have := (hA ((l : ℕ) : 𝓞 F)).mpr hw
    simpa using this
  haveI : IsAlgClosure ℚ (AlgebraicClosure F) := isAlgClosureQ F (AlgebraicClosure F)
  obtain ⟨j, hj⟩ := exists_emb (l := l) _ hAl
  exact ⟨j.comp (algebraMap F (AlgebraicClosure F)), fun x => by
    rw [← hA x, val_lt_one_iff hj]; rfl⟩

end Emb

variable (l) in
theorem exists_prim (N : ℕ) (hN : 0 < N) : ∃ ζ : PadicAlgCl l, IsPrimitiveRoot ζ N := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero (N : PadicAlgCl l) := ⟨by exact_mod_cast hN.ne'⟩
  first
  | exact HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl l) N
  | exact ⟨_, IsCyclotomicExtension.zeta_spec N (PadicAlgCl l) (PadicAlgCl l)⟩
  | exact ⟨_, IsCyclotomicExtension.zeta_spec ⟨N, hN⟩ (PadicAlgCl l) (PadicAlgCl l)⟩
  | exact IsAlgClosed.exists_primitiveRoot (PadicAlgCl l) N

def powHom {G : Type} [CommGroup G] (ζ : G) (N : ℕ) [NeZero N] (h : ζ ^ N = 1) :
    Multiplicative (ZMod N) →* G where
  toFun a := ζ ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, ← pow_add, ZMod.val_add]
    conv_rhs => rw [← Nat.div_add_mod ((Multiplicative.toAdd a).val + (Multiplicative.toAdd b).val) N,
      pow_add, pow_mul, h, one_pow, one_mul]

section Mu

variable (LL : FinExt l) {N : ℕ} [NeZero N] {ζ : PadicAlgCl l} (hζ : IsPrimitiveRoot ζ N) (hm : ζ ∈ LL.1)

include hζ in
theorem norm_prim : ‖ζ‖ = 1 := by
  first
  | exact hζ.norm'_eq_one (NeZero.ne N)
  | (have h := congrArg norm hζ.pow_eq_one
     rw [norm_pow, norm_one] at h
     exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne N)).mp h)

def zO : ↥(OL LL) := ⟨⟨ζ, hm⟩, (mem_OL LL _).mpr (norm_prim hζ).le⟩

theorem zO_pow : zO LL hζ hm ^ N = 1 := by
  first
  | (apply Subtype.ext; apply Subtype.ext; simp [zO, hζ.pow_eq_one])
  | (ext; simp [zO, hζ.pow_eq_one])

def zU : (↥(OL LL))ˣ := Units.ofPowEqOne (zO LL hζ hm) N (zO_pow LL hζ hm) (NeZero.ne N)

theorem zU_pow : zU LL hζ hm ^ N = 1 := by
  first
  | exact Units.ext (by simp [zU, zO_pow LL hζ hm])
  | (ext; simp [zU, zO_pow LL hζ hm])

def muHom : Multiplicative (ZMod N) →* (↥(OL LL))ˣ := powHom (zU LL hζ hm) N (zU_pow LL hζ hm)

theorem muHom_injective : Function.Injective (muHom LL hζ hm) := by
  intro a b h
  have h1 := congrArg (fun u : (↥(OL LL))ˣ => u.val.val.val) h
  have h2 : ζ ^ (Multiplicative.toAdd a).val = ζ ^ (Multiplicative.toAdd b).val := by
    simpa [muHom, powHom, zU, zO] using h1
  have h3 := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h2
  exact Multiplicative.toAdd.injective (ZMod.val_injective N h3)

end Mu

end Formalism.BasicNotions.Examples₂.LB
