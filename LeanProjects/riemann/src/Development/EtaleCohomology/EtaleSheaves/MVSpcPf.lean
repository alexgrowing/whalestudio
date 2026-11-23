import Development.EtaleCohomology.EtaleSheaves.PullInjOfIso
import Development.EtaleCohomology.TateTwists.EtaleSimplicialCochainShortExactSequenceHolds

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.MVSpcPf

def Ses : Prop := ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g → ∃ w,
  (ShortComplex.mk (biprod.lift ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g)))
    (biprod.desc ((chains R).map f) ((chains R).map g)) w).ShortExact

variable {R : Type} [CommRing R] {I : Cx R}

abbrev pc {K L : Cx R} (φ : K ⟶ L) {m : ℤ} (z : Cochain L I m) : Cochain K I m := (Cochain.ofHom φ).comp z (zero_add m)

theorem pc_comp {K L M : Cx R} (φ : K ⟶ L) (ψ : L ⟶ M) {m : ℤ} (z : Cochain M I m) : pc (φ ≫ ψ) z = pc φ (pc ψ z) := by
  simp [pc, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem pc_addm {K L : Cx R} (φ ψ : K ⟶ L) {m : ℤ} (z : Cochain L I m) : pc (φ + ψ) z = pc φ z + pc ψ z := by
  simp [pc, Cochain.ofHom_add, Cochain.add_comp]

theorem pc_negm {K L : Cx R} (φ : K ⟶ L) {m : ℤ} (z : Cochain L I m) : pc (-φ) z = -pc φ z := by
  simp [pc, Cochain.ofHom_neg, Cochain.neg_comp]

theorem pc_zerom {K L : Cx R} {m : ℤ} (z : Cochain L I m) : pc (0 : K ⟶ L) z = 0 := by
  simp [pc, Cochain.ofHom_zero, Cochain.zero_comp]

theorem pc_add {K L : Cx R} (φ : K ⟶ L) {m : ℤ} (z z' : Cochain L I m) : pc φ (z + z') = pc φ z + pc φ z' := by
  simp [pc, Cochain.comp_add]

theorem pc_sub {K L : Cx R} (φ : K ⟶ L) {m : ℤ} (z z' : Cochain L I m) : pc φ (z - z') = pc φ z - pc φ z' := by
  simp [pc, Cochain.comp_sub]

theorem pc_δ {K L : Cx R} (φ : K ⟶ L) {m : ℤ} (z : Cochain L I m) (m' : ℤ) : δ m m' (pc φ z) = pc φ (δ m m' z) :=
  δ_ofHom_comp φ z m'

theorem cpre_mk' {K L : Cx R} (φ : K ⟶ L) {m : ℤ} (z : Cocycle L I m) :
    cpre (Cocycle.ofHom φ) I m m (zero_add m) (CohomologyClass.mk z) =
      CohomologyClass.mk (Cocycle.mk (pc φ z.1) (m + 1) rfl (by rw [pc_δ, Cocycle.δ_eq_zero, pc, Cochain.comp_zero])) := by
  rw [cpre_mk]; congr 1

theorem cocy_δ {K : Cx R} {m : ℤ} (z : Cocycle K I m) (m' : ℤ) : δ m m' z.1 = 0 := by
  by_cases h : m + 1 = m'
  · exact (Cocycle.mem_iff m m' h z.1).1 z.2
  · exact δ_shape _ _ h _

theorem chase (hI : ∀ n, Injective (I.X n)) {K1 KA KB K3 : Cx R} (φ : K1 ⟶ KA) (ψ : K1 ⟶ KB) (u : KA ⟶ K3)
    (v : KB ⟶ K3) (w) (hS : (ShortComplex.mk (biprod.lift φ (-ψ)) (biprod.desc u v) w).ShortExact) (n : ℤ)
    (hc : ∀ c : CohomologyClass K1 I n, ∃ a b, c = cpre (Cocycle.ofHom φ) I n n (zero_add n) a -
      cpre (Cocycle.ofHom ψ) I n n (zero_add n) b)
    (x : CohomologyClass K3 I (n + 1)) (hu : cpre (Cocycle.ofHom u) I _ _ (zero_add _) x = 0)
    (hv : cpre (Cocycle.ofHom v) I _ _ (zero_add _) x = 0) : x = 0 := by
  have hC := fun m => LateralTheory.EtaleFoundations.etale_simplicial_cochain_short_exact_sequence_holds R I hI _ hS m
  obtain ⟨z, rfl⟩ := x.mk_surjective
  rw [cpre_mk', CohomologyClass.mk_eq_zero_iff] at hu hv
  obtain ⟨m, hm, aU, haU⟩ := hu
  obtain ⟨m', hm', aV, haV⟩ := hv
  have e1 : n = m := by omega
  subst e1
  have e2 : n = m' := by omega
  subst e2
  simp only [Cocycle.mk_coe] at haU haV
  set b : Cochain (KA ⊞ KB) I n := pc biprod.fst aU + pc biprod.snd aV with hbdef
  have hb : δ n (n + 1) b = pc (biprod.desc u v) z.1 := by
    rw [hbdef, δ_add, pc_δ, pc_δ, haU, haV, ← pc_comp, ← pc_comp, ← pc_addm, ← biprod.desc_eq]
  have hαb : δ n (n + 1) (pc (biprod.lift φ (-ψ)) b) = 0 := by
    rw [pc_δ, hb, ← pc_comp, w, pc_zerom]
  obtain ⟨a, b0, hab⟩ := hc (CohomologyClass.mk (Cocycle.mk (pc (biprod.lift φ (-ψ)) b) (n + 1) rfl hαb))
  obtain ⟨a, rfl⟩ := a.mk_surjective
  obtain ⟨b0, rfl⟩ := b0.mk_surjective
  rw [cpre_mk', cpre_mk', ← CohomologyClass.mk_sub, ← sub_eq_zero, ← CohomologyClass.mk_sub,
    CohomologyClass.mk_eq_zero_iff] at hab
  obtain ⟨k, hk, e, he⟩ := hab
  obtain ⟨e2, he2⟩ := (hC k).1 e
  set b2 : Cochain (KA ⊞ KB) I n := pc biprod.fst a.1 + pc biprod.snd b0.1 with hb2def
  have hαb2 : pc (biprod.lift φ (-ψ)) b2 = pc φ a.1 - pc ψ b0.1 := by
    rw [hb2def, pc_add, ← pc_comp, ← pc_comp, biprod.lift_fst, biprod.lift_snd, pc_negm, sub_eq_add_neg]
  have hδb2 : δ n (n + 1) b2 = 0 := by
    rw [hb2def, δ_add, pc_δ, pc_δ, cocy_δ, cocy_δ, pc, pc, Cochain.comp_zero, Cochain.comp_zero, add_zero]
  have hr : pc (biprod.lift φ (-ψ)) (b - b2 - δ k n e2) = 0 := by
    have he2' : pc (biprod.lift φ (-ψ)) e2 = e := he2
    rw [pc_sub, pc_sub, ← pc_δ, he2', he]
    change _ - _ - (pc (biprod.lift φ (-ψ)) b - (pc φ a.1 - pc ψ b0.1)) = 0
    rw [hαb2]; abel
  obtain ⟨c3, hc3⟩ := (hC n).2.1 _ hr
  have hc3' : pc (biprod.desc u v) c3 = _ := hc3
  have hz : pc (biprod.desc u v) (δ n (n + 1) c3 - z.1) = 0 := by
    rw [pc_sub, ← pc_δ]
    change δ n (n + 1) (pc (biprod.desc u v) c3) - _ = 0
    rw [hc3', δ_sub, δ_sub, δ_δ, hδb2, hb]; simp
  have := (hC (n + 1)).2.2 _ hz
  exact (CohomologyClass.mk_eq_zero_iff _).2 ⟨n, rfl, c3, sub_eq_zero.1 this⟩

end LateralTheory.E.MVSpcPf

open LateralTheory.E.MVSpcPf in
theorem LateralTheory.E.MVPf.MVSpc_of (hS : Ses) : LateralTheory.E.MVPf.MVSpc := by
  intro _ R _ F U V E f g hc n hd x hxf hxg
  obtain ⟨w, hw⟩ := hS R f g hc
  have hI : ∀ k, Injective ((res R F).X k) := fun k => by unfold res; infer_instance
  exact chase hI _ _ _ _ w hw n hd x hxf hxg
