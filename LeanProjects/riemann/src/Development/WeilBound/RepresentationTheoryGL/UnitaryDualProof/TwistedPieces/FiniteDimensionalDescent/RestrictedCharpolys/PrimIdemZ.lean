import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.FinrankImg

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.TP.Desc.Restr.PphiE

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Restr PositivityTheory.RgUd.TP.Desc.Restr.PphiA
  PositivityTheory.RgUd.TP.Desc.Restr.PphiB PositivityTheory.RgUd.TP.Desc.Restr.PphiC PositivityTheory.RgUd.TP.Desc.Restr.PphiD

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p c d : ℕ} [Fact p.Prime] [CharP k p] (B : FB k (p ^ c) d) {n : ℕ}

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem primIdem_Z' (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : primIdem (Z' B Z) = φ B '' primIdem Z := by
  have hinj := φ_inj B (n := n)
  have hZ : ∀ x, x ∈ Z' B Z ↔ ∃ y ∈ Z, φ B y = x := fun x => by
    rw [← SetLike.mem_coe, coe_Z', Set.mem_image]
    simp only [SetLike.mem_coe]
  have hidem : ∀ x : Matrix (Fin n) (Fin n) k, IsIdempotentElem (φ B x) ↔ IsIdempotentElem x := fun x => by
    show φ B x * φ B x = φ B x ↔ x * x = x
    rw [← map_mul]
    exact hinj.eq_iff
  ext e'
  constructor
  · rintro ⟨he'Z, hid, hne, hmin⟩
    obtain ⟨e, heZ, rfl⟩ := (hZ e').1 he'Z
    refine ⟨e, ⟨heZ, (hidem e).1 hid, fun h => hne (by rw [h, map_zero]), fun f hfZ hf hfe => ?_⟩, rfl⟩
    rcases hmin (φ B f) ((hZ _).2 ⟨f, hfZ, rfl⟩) ((hidem f).2 hf) (by rw [← map_mul, hfe]) with h | h
    · left
      exact hinj (by rw [h, map_zero])
    · right
      exact hinj h
  · rintro ⟨e, ⟨heZ, hid, hne, hmin⟩, rfl⟩
    refine ⟨(hZ _).2 ⟨e, heZ, rfl⟩, (hidem e).2 hid, fun h => hne (hinj (by rw [h, map_zero])),
      fun f' hf'Z hf' hfe => ?_⟩
    obtain ⟨f, hfZ, rfl⟩ := (hZ f').1 hf'Z
    rcases hmin f hfZ ((hidem f).1 hf') (hinj (by rw [map_mul, hfe])) with h | h
    · left
      rw [h, map_zero]
    · right
      rw [h]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem cen_map (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (e : Matrix (Fin n) (Fin n) k) :
    (cenSub (Z' B Z)).map (LinearMap.mulLeft k (φ B e)) = img B ((cenSub Z).map (LinearMap.mulLeft k e)) := by
  have hc : ∀ {m : ℕ} (W : Subalgebra k (Matrix (Fin m) (Fin m) k)) (x : Matrix (Fin m) (Fin m) k),
      x ∈ cenSub W ↔ x ∈ Bz W := fun W x => Iff.rfl
  have hcen := cen B Z
  ext y
  constructor
  · rintro ⟨x', hx', rfl⟩
    have h1 : x' ∈ φ B '' Bz Z := by
      rw [← hcen]
      exact (hc _ _).1 hx'
    obtain ⟨x, hx, rfl⟩ := h1
    exact ⟨e * x, ⟨x, (hc _ _).2 hx, rfl⟩, by
      show φ B (e * x) = φ B e * φ B x
      exact map_mul _ _ _⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have h1 : φ B x ∈ Bz (Z' B Z) := by
      rw [hcen]
      exact ⟨x, (hc _ _).1 hx, rfl⟩
    exact ⟨φ B x, (hc _ _).2 h1, by
      show φ B e * φ B x = φ B (e * x)
      exact (map_mul _ _ _).symm⟩

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem z_map (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (e : Matrix (Fin n) (Fin n) k) :
    (Z' B Z).toSubmodule.map (LinearMap.mulLeft k (φ B e)) = img B (Z.toSubmodule.map (LinearMap.mulLeft k e)) := by
  have hZ : ∀ x, x ∈ Z' B Z ↔ ∃ y ∈ Z, φ B y = x := fun x => by
    rw [← SetLike.mem_coe, coe_Z', Set.mem_image]
    simp only [SetLike.mem_coe]
  ext y
  constructor
  · rintro ⟨x', hx', rfl⟩
    obtain ⟨x, hx, rfl⟩ := (hZ x').1 hx'
    exact ⟨e * x, ⟨x, hx, rfl⟩, by
      show φ B (e * x) = φ B e * φ B x
      exact map_mul _ _ _⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨φ B x, (hZ _).2 ⟨x, hx, rfl⟩, by
      show φ B e * φ B x = φ B (e * x)
      exact (map_mul _ _ _).symm⟩

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem mu_Z' (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : mu (Z' B Z) = mu Z := by
  unfold mu
  rw [primIdem_Z', finsum_mem_image (fun x _ y _ h => φ_inj B h)]
  refine finsum_mem_congr rfl fun e _ => ?_
  rw [cen_map, z_map, finrank_img, finrank_img]
  exact Nat.mul_div_mul_left _ _ (d_pos B)

end PositivityTheory.RgUd.TP.Desc.Restr.PphiE
