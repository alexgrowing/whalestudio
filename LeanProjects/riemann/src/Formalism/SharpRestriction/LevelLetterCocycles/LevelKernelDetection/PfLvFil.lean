import Formalism.SharpRestriction.LevelLetterCocycles.FinalLevelsOf

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct Formalism.MainNotions.N.Ln03

section Period

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem lvFil_Fil_anti {a b : ℤ} (hab : a ≤ b) : PD.Fil b ≤ PD.Fil a := by
  obtain ⟨k, rfl⟩ := Int.le.dest hab
  clear hab
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show a + ((k + 1 : ℕ) : ℤ) = a + k + 1 by push_cast; ring]
    exact (PD.Fil_anti (a + k)).trans ih

theorem lvFil_FilV_anti : Antitone (FilV PD (LL := LL) (V := V)) := by
  intro a b hab
  have h : (PD.Fil b).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp := lvFil_Fil_anti PD hab
  unfold FilV
  rw [← Submodule.subtype_comp_inclusion _ _ h]
  have e : AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
      (((PD.Fil a).restrictScalars Qp).subtype ∘ₗ Submodule.inclusion h) =
      AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) ((PD.Fil a).restrictScalars Qp).subtype ∘ₗ
        AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (Submodule.inclusion h) := by
    rw [← AlgebraTensorModule.map_comp, LinearMap.id_comp]
  rw [e]
  exact LinearMap.range_comp_le_range _ _

theorem lvFil_FilCris_anti (ρ : Representation LL G V) : Antitone (FilCris PD ρ) := by
  intro a b hab
  exact inf_le_inf_left _ (Submodule.comap_mono (lvFil_FilV_anti PD hab))

theorem lvFil_tensor_injective {N₁ N₂ : Type} [AddCommGroup N₁] [Module Qp N₁] [AddCommGroup N₂] [Module Qp N₂]
    (g : N₁ →ₗ[Qp] N₂) (hg : Function.Injective g) :
    Function.Injective (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) g) := by
  have e : ⇑(AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) g) = ⇑(g.lTensor V) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [e]
  exact Module.Flat.lTensor_preserves_injective_linearMap g hg

theorem lvFil_ιV_injective : Function.Injective (ιV PD (LL := LL) (V := V)) := by
  unfold ιV
  exact lvFil_tensor_injective (PD.ι.toLinearMap.restrictScalars Qp) PD.ι_inj

theorem lvFil_φVB_injective : Function.Injective (φVB PD (LL := LL) (V := V)) := by
  unfold φVB
  exact lvFil_tensor_injective PD.φ.toLinearMap PD.φ_inj

theorem lvFil_φ_act (ρ : Representation LL G V) (g : G) (x : V ⊗[Qp] B) :
    φVB PD (LL := LL) (V := V) (actVB PD ρ g x) = actVB PD ρ g (φVB PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [φVB, actVB, PD.φ_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem lvFil_φ_Dcris (ρ : Representation LL G V) {x : V ⊗[Qp] B} (hx : x ∈ Dcris PD ρ) :
    φVB PD (LL := LL) (V := V) x ∈ Dcris PD ρ := by
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hx ⊢
  intro g
  rw [← lvFil_φ_act, hx g]

theorem lvFil_φ_mul (c : K₀) (x : V ⊗[Qp] B) :
    φVB PD (LL := LL) (V := V) (mulVB (LL := LL) (V := V) (B := B) c x) = mulVB (LL := LL) (V := V) (B := B) (PD.σ c) (φVB PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [φVB, mulVB, PD.φ_K₀]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem lvFil_FilV_exh (y : V ⊗[Qp] BdR) : ∃ a, y ∈ FilV PD (LL := LL) (V := V) a := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, zero_mem _⟩
  | tmul v b =>
    obtain ⟨a, ha⟩ := PD.Fil_exh b
    exact ⟨a, ⟨v ⊗ₜ ⟨b, ha⟩, by simp⟩⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, add_mem (lvFil_FilV_anti PD (min_le_left a b) ha)
      (lvFil_FilV_anti PD (min_le_right a b) hb)⟩

theorem lvFil_FilV_sep (y : V ⊗[Qp] BdR) (hy : ∀ a, y ∈ FilV PD (LL := LL) (V := V) a) : y = 0 := by
  classical
  let bV := Module.Free.chooseBasis Qp V
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := BdR) bV
  have hc : ∀ a, ∀ z ∈ FilV PD (LL := LL) (V := V) a, ∀ i, e z i ∈ PD.Fil a := by
    intro a z hz i
    obtain ⟨t, rfl⟩ := hz
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul v f =>
      simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, Submodule.subtype_apply, e,
        TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
      exact (PD.Fil a).smul_of_tower_mem _ f.2
    | add x y hx hy =>
      rw [map_add, map_add, Finsupp.add_apply]
      exact add_mem hx hy
  have h0 : e y = 0 := by
    ext i
    exact PD.Fil_sep _ (fun a => hc a y (hy a) i)
  exact e.injective (by rw [h0, map_zero])

theorem lvFil_exh_sub (ℓ : Submodule LL (V ⊗[Qp] B)) [FiniteDimensional LL ℓ] :
    ∃ lo : ℤ, ∀ x ∈ ℓ, ιV PD (LL := LL) (V := V) x ∈ FilV PD (LL := LL) (V := V) lo := by
  let S : ℤ → Submodule LL ℓ := fun a => (FilV PD (LL := LL) (V := V) a).comap ((ιV PD (LL := LL) (V := V)).comp ℓ.subtype)
  have hS : Antitone S := fun a b h => Submodule.comap_mono (lvFil_FilV_anti PD h)
  obtain ⟨k0, hk0⟩ := (monotone_stabilizes_iff_noetherian.mpr inferInstance)
    (⟨fun k : ℕ => S (-(k : ℤ)), fun i j h => hS (by simp only [neg_le_neg_iff]; exact_mod_cast h)⟩ :
      ℕ →o Submodule LL ℓ)
  refine ⟨-(k0 : ℤ), fun x hx => ?_⟩
  obtain ⟨a, ha⟩ := lvFil_FilV_exh PD (LL := LL) (ιV PD (LL := LL) (V := V) x)
  have h1 : (⟨x, hx⟩ : ℓ) ∈ S a := ha
  have h2 : S a ≤ S (-((k0 + (-a).toNat : ℕ) : ℤ)) := hS (by push_cast; omega)
  have h3 : S (-(k0 : ℤ)) = S (-((k0 + (-a).toNat : ℕ) : ℤ)) := hk0 (k0 + (-a).toNat) (by omega)
  rw [← h3] at h2
  exact h2 h1

theorem lvFil_sep_sub (ℓ : Submodule LL (V ⊗[Qp] B)) [FiniteDimensional LL ℓ] :
    ∃ hi : ℤ, ∀ x ∈ ℓ, ιV PD (LL := LL) (V := V) x ∈ FilV PD (LL := LL) (V := V) hi → x = 0 := by
  let S : ℤ → Submodule LL ℓ := fun a => (FilV PD (LL := LL) (V := V) a).comap ((ιV PD (LL := LL) (V := V)).comp ℓ.subtype)
  have hS : Antitone S := fun a b h => Submodule.comap_mono (lvFil_FilV_anti PD h)
  obtain ⟨k0, hk0⟩ := IsArtinian.monotone_stabilizes
    (⟨fun k : ℕ => OrderDual.toDual (S k), fun i j h => OrderDual.toDual_le_toDual.mpr
      (hS (by exact_mod_cast h))⟩ : ℕ →o (Submodule LL ℓ)ᵒᵈ)
  refine ⟨k0, fun x hx hxk => ?_⟩
  have hall : ∀ a, ιV PD (LL := LL) (V := V) x ∈ FilV PD (LL := LL) (V := V) a := by
    intro a
    have h1 : (⟨x, hx⟩ : ℓ) ∈ S k0 := hxk
    have h3 : OrderDual.toDual (S k0) = OrderDual.toDual (S ((k0 + a.toNat : ℕ) : ℤ)) :=
      hk0 (k0 + a.toNat) (by omega)
    have h4 : S k0 = S ((k0 + a.toNat : ℕ) : ℤ) := OrderDual.toDual.injective h3
    have h5 : S ((k0 + a.toNat : ℕ) : ℤ) ≤ S a := hS (by push_cast; omega)
    exact h5 (h4 ▸ h1)
  exact lvFil_ιV_injective PD (by rw [map_zero]; exact lvFil_FilV_sep PD _ hall)

theorem lvFil_fin_of_isCrys (ρ : Representation LL G V) [FiniteDimensional LL V] (h : IsCrys PD ρ) :
    FiniteDimensional LL ↥(Dcris PD ρ) := by
  have := PD.finK₀
  by_cases hV : Module.finrank LL V = 0
  · have : Subsingleton V := Module.finrank_zero_iff.mp hV
    have hz : ∀ x : V ⊗[Qp] B, x = 0 := fun x => by
      induction x using TensorProduct.induction_on with
      | zero => rfl
      | tmul a b => rw [Subsingleton.elim a 0, zero_tmul]
      | add x y hx hy => rw [hx, hy, add_zero]
    have : Subsingleton ↥(Dcris PD ρ) := ⟨fun x y => Subtype.ext (by rw [hz x, hz y])⟩
    infer_instance
  · apply Module.finite_of_finrank_pos
    rw [h]
    exact Nat.mul_pos Module.finrank_pos (Nat.pos_of_ne_zero hV)

end Period

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    {W : LocWach PD LL O v n} {T : LocLat G Qp LL O} {c : ZMod n}

theorem filAnti_holds : ∀ s, Antitone (FilD W T c s) := by
  intro s a b hab
  unfold FilD FilLev
  exact Submodule.comap_mono (Submodule.map_mono (Submodule.map_mono
    (inf_le_inf_right _ (lvFil_FilCris_anti PD T.ρ hab))))

theorem lvFil_φ_letter (i : ZMod n) {x : T.V ⊗[Qp] B} (hx : x ∈ DcrisL PD T.ρ (W.emb i)) :
    φVB PD (LL := LL) (V := T.V) x ∈ DcrisL PD T.ρ (W.emb (i + 1)) := by
  simp only [DcrisL, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hx ⊢
  refine ⟨lvFil_φ_Dcris PD T.ρ hx.1, fun c' => ?_⟩
  obtain ⟨c₀, rfl⟩ := PD.σ_bij.2 c'
  rw [← lvFil_φ_mul, hx.2 c₀, map_smul, ← DFunLike.congr_fun (W.emb_σ i) c₀]
  rfl

theorem lvFil_φpow_letter (i : ZMod n) (s : ℕ) {x : T.V ⊗[Qp] B} (hx : x ∈ DcrisL PD T.ρ (W.emb i)) :
    ((φVB PD (LL := LL) (V := T.V) : Module.End LL (T.V ⊗[Qp] B)) ^ s) x ∈ DcrisL PD T.ρ (W.emb (i + s)) := by
  induction s with
  | zero => simpa using hx
  | succ s ih =>
    have h := lvFil_φ_letter (W := W) (T := T) _ ih
    rw [show i + ((s + 1 : ℕ) : ZMod n) = i + s + 1 by push_cast; ring, pow_succ']
    exact h

theorem lvFil_letter_fin (hfin : FiniteDimensional LL ↥(Dcris PD T.ρ)) (i : ZMod n) :
    FiniteDimensional LL ↥(DcrisL PD T.ρ (W.emb i)) :=
  Module.Finite.of_injective (Submodule.inclusion (inf_le_left : DcrisL PD T.ρ (W.emb i) ≤ Dcris PD T.ρ))
    (Submodule.inclusion_injective _)

theorem lvFil_finrank_step (hfin : FiniteDimensional LL ↥(Dcris PD T.ρ)) (i : ZMod n) :
    Module.finrank LL ↥(DcrisL PD T.ρ (W.emb i)) ≤ Module.finrank LL ↥(DcrisL PD T.ρ (W.emb (i + 1))) := by
  have := lvFil_letter_fin (W := W) hfin (i + 1)
  refine LinearMap.finrank_le_finrank_of_injective
    (f := (φVB PD (LL := LL) (V := T.V)).restrict (fun x hx => lvFil_φ_letter (W := W) (T := T) i hx)) ?_
  intro x y hxy
  exact Subtype.ext (lvFil_φVB_injective PD (congrArg Subtype.val hxy))

theorem lvFil_finrank_le (hfin : FiniteDimensional LL ↥(Dcris PD T.ρ)) (i : ZMod n) (k : ℕ) :
    Module.finrank LL ↥(DcrisL PD T.ρ (W.emb i)) ≤ Module.finrank LL ↥(DcrisL PD T.ρ (W.emb (i + k))) := by
  induction k with
  | zero => rw [show i + ((0 : ℕ) : ZMod n) = i by simp]
  | succ k ih =>
    have h := lvFil_finrank_step (W := W) hfin (i + k)
    rw [show i + (k : ZMod n) + 1 = i + ((k + 1 : ℕ) : ZMod n) by push_cast; ring] at h
    exact ih.trans h

theorem lvFil_finrank_eq (hfin : FiniteDimensional LL ↥(Dcris PD T.ρ)) (i : ZMod n) (k : ℕ) :
    Module.finrank LL ↥(DcrisL PD T.ρ (W.emb (i + k))) = Module.finrank LL ↥(DcrisL PD T.ρ (W.emb i)) := by
  apply le_antisymm _ (lvFil_finrank_le hfin i k)
  have h := lvFil_finrank_le (W := W) hfin (i + k) (n * k - k)
  have hn : 1 ≤ n := NeZero.one_le
  have e : i + (k : ZMod n) + ((n * k - k : ℕ) : ZMod n) = i := by
    rw [Nat.cast_sub (Nat.le_mul_of_pos_left k hn), Nat.cast_mul, ZMod.natCast_self]
    ring
  rwa [e] at h

theorem lvFil_φpow_surj (hfin : FiniteDimensional LL ↥(Dcris PD T.ρ)) (s : ℕ) (y : T.V ⊗[Qp] B)
    (hy : y ∈ DcrisL PD T.ρ (W.emb c)) :
    ∃ x ∈ DcrisL PD T.ρ (W.emb (c - s)), ((φVB PD (LL := LL) (V := T.V) : Module.End LL (T.V ⊗[Qp] B)) ^ s) x = y := by
  have h1 := lvFil_letter_fin (W := W) hfin (c - s)
  have h2 := lvFil_letter_fin (W := W) hfin c
  have hmap : ∀ x ∈ DcrisL PD T.ρ (W.emb (c - s)),
      ((φVB PD (LL := LL) (V := T.V) : Module.End LL (T.V ⊗[Qp] B)) ^ s) x ∈ DcrisL PD T.ρ (W.emb c) := by
    intro x hx
    have := lvFil_φpow_letter (W := W) (T := T) (c - s) s hx
    rwa [sub_add_cancel] at this
  let f := ((φVB PD (LL := LL) (V := T.V) : Module.End LL (T.V ⊗[Qp] B)) ^ s).restrict hmap
  have hinj : Function.Injective f := by
    intro x x' hxx
    apply Subtype.ext
    have hi : Function.Injective ⇑((φVB PD (LL := LL) (V := T.V) : Module.End LL (T.V ⊗[Qp] B)) ^ s) := by
      rw [Module.End.coe_pow]; exact (lvFil_φVB_injective PD).iterate s
    exact hi (congrArg Subtype.val hxx)
  have hrk : Module.finrank LL ↥(DcrisL PD T.ρ (W.emb (c - s))) = Module.finrank LL ↥(DcrisL PD T.ρ (W.emb c)) := by
    have := lvFil_finrank_eq (W := W) hfin (c - s) s
    rw [sub_add_cancel] at this
    exact this.symm
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrk).mp hinj ⟨y, hy⟩
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

theorem filt_holds (ell : ℕ) (hfin : FiniteDimensional LL ↥(Dcris PD T.ρ)) :
    ∀ s < ell, IsFilt (FilD W T c s) := by
  intro s _
  have h1 := lvFil_letter_fin (W := W) hfin (c - s)
  obtain ⟨lo, hlo⟩ := lvFil_exh_sub PD (DcrisL PD T.ρ (W.emb (c - s)))
  obtain ⟨hi, hhi⟩ := lvFil_sep_sub PD (DcrisL PD T.ρ (W.emb (c - s)))
  refine ⟨filAnti_holds s, ⟨lo, ?_⟩, ⟨hi, ?_⟩⟩
  · rw [eq_top_iff]
    rintro ⟨d, hd⟩ -
    obtain ⟨y, hy, rfl⟩ := lvFil_φpow_surj (W := W) hfin s d hd
    simp only [FilD, FilLev, Submodule.mem_comap, LinearMap.comp_apply, Submodule.subtype_apply]
    exact Submodule.mem_map_of_mem (Submodule.mem_map_of_mem
      (Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hy).1, hlo y hy⟩, hy⟩))
  · rw [eq_bot_iff]
    rintro ⟨d, hd⟩ hdF
    simp only [FilD, FilLev, Submodule.mem_comap, LinearMap.comp_apply, Submodule.subtype_apply,
      Submodule.mem_map, Submodule.mem_inf, FilCris] at hdF
    obtain ⟨w, ⟨y, ⟨⟨-, hyF⟩, hyl⟩, rfl⟩, hw⟩ := hdF
    have hy0 : y = 0 := hhi y hyl hyF
    subst hy0
    have hd0 : d = 0 := lvFil_ιV_injective PD (by rw [← hw]; simp)
    subst hd0
    exact (Submodule.mem_bot LL).mpr rfl

end Formalism.MainNotions.N.Ln03.Pf
