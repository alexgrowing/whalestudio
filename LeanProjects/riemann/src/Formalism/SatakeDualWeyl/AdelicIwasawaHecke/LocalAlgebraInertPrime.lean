import Formalism.SatakeDualWeyl.StatementG
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Transport
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stabstd
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelvsplit

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG

section Gen

variable {A L : Type} [CommRing A] [CommRing L] {n : Type} [Fintype n] [DecidableEq n]

theorem gLoc_bc_coe (e : A →+* L) (g : GL n A) :
    ((bc (n := n) e g : GL n L) : Matrix n n L) = (g : Matrix n n A).map e := rfl

theorem gLoc_bc_symm (e : A ≃+* L) (g : GL n L) :
    bc (n := n) (e : A →+* L) (bc (n := n) (e.symm : L →+* A) g) = g := by
  ext i j
  simp [bc]

theorem gLoc_bc_inj (e : A ≃+* L) : Function.Injective (bc (n := n) (e : A →+* L)) := by
  intro g h hgh
  ext i j
  have := congrArg (fun u : GL n L => (u : Matrix n n L) i j) hgh
  simpa [bc] using this

theorem gLoc_mem_one_iff (σA : A →+* A) (σL : L →+* L) (e : A ≃+* L)
    (he : ∀ x, e (σA x) = σL (e x)) (g : GL n A) :
    g ∈ UJ σA (1 : Matrix n n A) ↔ bc (e : A →+* L) g ∈ UJ σL (1 : Matrix n n L) := by
  set f : A →+* L := (e : A →+* L)
  have hf : Function.Injective f := e.injective
  have hc : (RingHom.mapMatrix f) (cT σA (g : Matrix n n A)) =
      cT σL (RingHom.mapMatrix f (g : Matrix n n A)) := by
    ext i j
    simp [cT, f, he]
  show cT σA (g : Matrix n n A) * 1 * (g : Matrix n n A) = 1 ↔
    cT σL (RingHom.mapMatrix f (g : Matrix n n A)) * 1 * RingHom.mapMatrix f (g : Matrix n n A) = 1
  rw [← hc, ← map_one (RingHom.mapMatrix f), ← map_mul, ← map_mul, map_one]
  constructor
  · intro h
    rw [h, map_one]
  · intro h
    apply Matrix.map_injective hf
    simpa [RingHom.mapMatrix_apply] using h

theorem gLoc_conj_iff (σL : L →+* L) (J : Matrix n n L) (P : GL n L)
    (hP : cT σL (P : Matrix n n L) * (P : Matrix n n L) = J) (g : GL n L) :
    g ∈ UJ σL (1 : Matrix n n L) ↔ P⁻¹ * g * P ∈ UJ σL J := by
  set p : Matrix n n L := (P : Matrix n n L)
  set q : Matrix n n L := ((P⁻¹ : GL n L) : Matrix n n L)
  set G : Matrix n n L := (g : Matrix n n L)
  have hpq : p * q = 1 := by
    simp only [p, q]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hqp : q * p = 1 := by
    simp only [p, q]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have cq : cT σL q * cT σL p = 1 := by rw [← cT_mul, hpq, cT_one]
  have cancel : ∀ X, cT σL q * (cT σL p * X * p) * q = X := fun X => by
    calc cT σL q * (cT σL p * X * p) * q = (cT σL q * cT σL p) * X * (p * q) := by
          simp only [Matrix.mul_assoc]
      _ = X := by rw [cq, hpq, Matrix.one_mul, Matrix.mul_one]
  have inj : ∀ X Y, cT σL p * X * p = cT σL p * Y * p → X = Y := fun X Y h => by
    rw [← cancel X, ← cancel Y, h]
  have E : cT σL (q * G * p) * (cT σL p * p) * (q * G * p) = cT σL p * (cT σL G * G) * p := by
    rw [cT_mul, cT_mul]
    calc cT σL p * (cT σL G * cT σL q) * (cT σL p * p) * (q * G * p)
        = cT σL p * (cT σL G * ((cT σL q * cT σL p) * (p * q)) * G) * p := by
          simp only [Matrix.mul_assoc]
      _ = cT σL p * (cT σL G * G) * p := by rw [cq, hpq, Matrix.one_mul, Matrix.mul_one]
  show cT σL G * 1 * G = 1 ↔
    cT σL (((P⁻¹ * g * P : GL n L)) : Matrix n n L) * J * ((P⁻¹ * g * P : GL n L) : Matrix n n L) = J
  rw [show (((P⁻¹ * g * P : GL n L)) : Matrix n n L) = q * G * p by simp only [Units.val_mul, p, q, G]]
  rw [← hP, E, Matrix.mul_one]
  constructor
  · intro h
    rw [h, Matrix.mul_one]
  · intro h
    exact inj _ _ (by rw [h, Matrix.mul_one])

end Gen

section Int

variable {A L : Type} [CommRing A] [CommRing L] {n : Type} [Fintype n] [DecidableEq n]

theorem gLoc_range_subtype {R : Type} [CommRing R] (S : Subring R) (x : R) :
    x ∈ Set.range S.subtype ↔ x ∈ S := by
  exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

theorem gLoc_int_iff (e : A ≃+* L) (T : Subring A) (O : Subring L) (hT : ∀ x, x ∈ T ↔ e x ∈ O)
    (g : GL n A) :
    g ∈ (bc (n := n) T.subtype).range ↔ bc (e : A →+* L) g ∈ (bc (n := n) O.subtype).range := by
  have key : ∀ {B : Type} [CommRing B] (S : Subring B) (u : GL n B),
      u ∈ (bc (n := n) S.subtype).range ↔ (∀ i j, (u : Matrix n n B) i j ∈ S) ∧
        (∀ i j, ((u⁻¹ : GL n B) : Matrix n n B) i j ∈ S) := by
    intro B _ S u
    constructor
    · rintro ⟨h, rfl⟩
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · simp [bc]
      · rw [← map_inv]
        simp [bc]
    · rintro ⟨h1, h2⟩
      have hinj : Function.Injective (RingHom.mapMatrix S.subtype : Matrix n n S → Matrix n n B) :=
        Matrix.map_injective Subtype.val_injective
      let Am : Matrix n n S := Matrix.of fun i j => ⟨(u : Matrix n n B) i j, h1 i j⟩
      let Bm : Matrix n n S := Matrix.of fun i j => ⟨((u⁻¹ : GL n B) : Matrix n n B) i j, h2 i j⟩
      have hA : RingHom.mapMatrix S.subtype Am = (u : Matrix n n B) := by ext i j; rfl
      have hB : RingHom.mapMatrix S.subtype Bm = ((u⁻¹ : GL n B) : Matrix n n B) := by ext i j; rfl
      refine ⟨⟨Am, Bm, hinj ?_, hinj ?_⟩, ?_⟩
      · rw [map_mul, hA, hB, map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      · rw [map_mul, hA, hB, map_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      · ext i j
        rfl
  rw [key T g, key O (bc (e : A →+* L) g), ← map_inv]
  simp only [gLoc_bc_coe, Matrix.map_apply, RingEquiv.coe_toRingHom, ← hT]

theorem gLoc_conj_mem {G : Type} [Group G] (K : Subgroup G) (P : G) (hP : P ∈ K) (g : G) :
    g ∈ K ↔ P⁻¹ * g * P ∈ K := by
  constructor
  · intro h
    exact K.mul_mem (K.mul_mem (K.inv_mem hP) h) hP
  · intro h
    have := K.mul_mem (K.mul_mem hP h) (K.inv_mem hP)
    simpa [mul_assoc] using this

end Int

section Main

variable {A L : Type} [CommRing A] [Field L] [Valued L (WithZero (Multiplicative ℤ))] {m : ℕ}

def gLoc_hom (σA : A →+* A) (σL : L →+* L) (e : A ≃+* L) (he : ∀ x, e (σA x) = σL (e x))
    (P : GL (Fin m) L)
    (hP : cT σL (P : Matrix (Fin m) (Fin m) L) * (P : Matrix (Fin m) (Fin m) L) = antiJ L m)
    (H : Subgroup (GL (Fin m) A)) (hH : ∀ g, g ∈ H ↔ g ∈ UJ σA (1 : Matrix (Fin m) (Fin m) A)) :
    H →* GU σL m where
  toFun x := ⟨P⁻¹ * bc (e : A →+* L) (x : GL (Fin m) A) * P,
    (gLoc_conj_iff σL _ P hP _).1 ((gLoc_mem_one_iff σA σL e he _).1 ((hH _).1 x.2))⟩
  map_one' := by
    apply Subtype.ext
    show P⁻¹ * bc (e : A →+* L) (1 : GL (Fin m) A) * P = 1
    rw [map_one, mul_one, inv_mul_cancel]
  map_mul' a b := by
    apply Subtype.ext
    show P⁻¹ * bc (e : A →+* L) ((a : GL (Fin m) A) * (b : GL (Fin m) A)) * P =
      (P⁻¹ * bc (e : A →+* L) (a : GL (Fin m) A) * P) * (P⁻¹ * bc (e : A →+* L) (b : GL (Fin m) A) * P)
    rw [map_mul]
    simp only [mul_assoc, mul_inv_cancel_left]

theorem gLoc_hom_apply (σA : A →+* A) (σL : L →+* L) (e : A ≃+* L) (he : ∀ x, e (σA x) = σL (e x))
    (P : GL (Fin m) L)
    (hP : cT σL (P : Matrix (Fin m) (Fin m) L) * (P : Matrix (Fin m) (Fin m) L) = antiJ L m)
    (H : Subgroup (GL (Fin m) A)) (hH : ∀ g, g ∈ H ↔ g ∈ UJ σA (1 : Matrix (Fin m) (Fin m) A))
    (x : H) :
    ((gLoc_hom σA σL e he P hP H hH x : GU σL m) : GL (Fin m) L) =
      P⁻¹ * bc (e : A →+* L) (x : GL (Fin m) A) * P := rfl

theorem gLoc_hom_bij (σA : A →+* A) (σL : L →+* L) (e : A ≃+* L) (he : ∀ x, e (σA x) = σL (e x))
    (P : GL (Fin m) L)
    (hP : cT σL (P : Matrix (Fin m) (Fin m) L) * (P : Matrix (Fin m) (Fin m) L) = antiJ L m)
    (H : Subgroup (GL (Fin m) A)) (hH : ∀ g, g ∈ H ↔ g ∈ UJ σA (1 : Matrix (Fin m) (Fin m) A)) :
    Function.Bijective (gLoc_hom σA σL e he P hP H hH) := by
  constructor
  · intro x y hxy
    have h1 := congrArg (fun z : GU σL m => P * (z : GL (Fin m) L) * P⁻¹) hxy
    simp only [gLoc_hom_apply] at h1
    have h2 : bc (e : A →+* L) (x : GL (Fin m) A) = bc (e : A →+* L) (y : GL (Fin m) A) := by
      simpa [mul_assoc] using h1
    exact Subtype.ext (gLoc_bc_inj e h2)
  · intro y
    have hbg : bc (e : A →+* L) (bc (e.symm : L →+* A) (P * (y : GL (Fin m) L) * P⁻¹)) =
        P * (y : GL (Fin m) L) * P⁻¹ := gLoc_bc_symm e _
    have hmem : bc (e.symm : L →+* A) (P * (y : GL (Fin m) L) * P⁻¹) ∈ H := by
      rw [hH, gLoc_mem_one_iff σA σL e he, hbg, gLoc_conj_iff σL _ P hP]
      simpa [mul_assoc] using y.2
    refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    rw [gLoc_hom_apply, hbg]
    group

theorem gLoc_level (e : A ≃+* L) (T : Subring A) (hT : ∀ x, x ∈ T ↔ e x ∈ intL L) (P : GL (Fin m) L)
    (hPO : P ∈ (bc (n := Fin m) (intL L).subtype).range) {σL : L →+* L}
    (H Lv : Subgroup (GL (Fin m) A))
    (hLv : ∀ g, g ∈ Lv ↔ g ∈ H ∧ g ∈ (bc (n := Fin m) T.subtype).range)
    (f : H ≃* GU σL m) (hf : ∀ x, ((f x : GU σL m) : GL (Fin m) L) = P⁻¹ * bc (e : A →+* L) x * P) :
    (Lv.subgroupOf H).map f.toMonoidHom = KU σL m := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨-, hxT⟩ := (hLv _).mp (Subgroup.mem_subgroupOf.mp hx)
    rw [KU, Subgroup.mem_subgroupOf, intPts, Subgroup.mem_inf]
    refine ⟨(f x).2, ?_⟩
    show ((f x : GU σL m) : GL (Fin m) L) ∈ _
    rw [hf]
    exact (gLoc_conj_mem _ P hPO _).mp ((gLoc_int_iff e T (intL L) hT _).mp hxT)
  · intro hy
    obtain ⟨x, rfl⟩ := f.surjective y
    refine ⟨x, ?_, rfl⟩
    refine Subgroup.mem_subgroupOf.mpr ((hLv _).mpr ⟨x.2, ?_⟩)
    rw [KU, Subgroup.mem_subgroupOf, intPts, Subgroup.mem_inf] at hy
    have h2 := hy.2
    change ((f x : GU σL m) : GL (Fin m) L) ∈ _ at h2
    rw [hf] at h2
    exact (gLoc_int_iff e T (intL L) hT _).mpr ((gLoc_conj_mem _ P hPO _).mpr h2)

theorem gLoc_main (σA : A →+* A) (σL : L →+* L) (e : A ≃+* L) (he : ∀ x, e (σA x) = σL (e x))
    (T : Subring A) (hT : ∀ x, x ∈ T ↔ e x ∈ intL L) (P : GL (Fin m) L)
    (hPO : P ∈ (bc (n := Fin m) (intL L).subtype).range)
    (hP : cT σL (P : Matrix (Fin m) (Fin m) L) * (P : Matrix (Fin m) (Fin m) L) = antiJ L m)
    (H Lv : Subgroup (GL (Fin m) A)) (hH : ∀ g, g ∈ H ↔ g ∈ UJ σA (1 : Matrix (Fin m) (Fin m) A))
    (hLv : ∀ g, g ∈ Lv ↔ g ∈ H ∧ g ∈ (bc (n := Fin m) T.subtype).range) :
    ∃ f : H ≃* GU σL m,
      (∀ x, ((f x : GU σL m) : GL (Fin m) L) = P⁻¹ * bc (e : A →+* L) x * P) ∧
      (Lv.subgroupOf H).map f.toMonoidHom = KU σL m := by
  refine ⟨MulEquiv.ofBijective (gLoc_hom σA σL e he P hP H hH) (gLoc_hom_bij σA σL e he P hP H hH),
    fun x => rfl, ?_⟩
  exact gLoc_level e T hT P hPO H Lv hLv _ (fun x => rfl)

end Main

theorem local_algebra_inert_prime : Formalism.UG.LocInert := by
  intro F E _ _ _ _ _ σ n v L _ _ _ e σw P he hT hPO hP
  have hH : ∀ g, g ∈ UPts σ (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) ↔
      g ∈ UJ (sigR σ (v.adicCompletion F)) (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) := by
    intro g
    rw [UPts, Matrix.map_one _ (map_zero _) (map_one _)]
  have hLv : ∀ g, g ∈ levelV σ (1 : Matrix (Fin n) (Fin n) E) v ↔
      g ∈ UPts σ (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) ∧
      g ∈ (bc (n := Fin n) (tensInt (F := F) (v.adicCompletion F) (intOE E) (Ov F v)).subtype).range := by
    intro g
    rw [levelV, level, Subgroup.mem_inf,
      stabilizer_standard_lattice _ _ (Fin n) (fun a b h => Subtype.ext h)]
    rfl
  obtain ⟨f, hf1, hf2⟩ := gLoc_main (sigR σ (v.adicCompletion F)) σw e he _ hT P hPO hP _ _ hH hLv
  exact ⟨f, hf1, hf2⟩

end Formalism.UG.P
